"""Replay the three-residual-edge proof and its controls offline on macOS."""
import argparse
import importlib.util
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

DEFAULT_TARGETS = ("ThreeMatchingBound", "MatchControls")
ORDERS = ("AAOO", "AOAO", "AOOA", "OAAO", "OAOA", "OOAA")
MATCH_CASES = {"MatchCase" + order for order in ORDERS}
DRIVER = Path(__file__).resolve().parent.parent / "disjoint" / "replay.py"


def load_driver():
    spec = importlib.util.spec_from_file_location("two_touching_replay", DRIVER)
    if spec is None or spec.loader is None:
        raise ImportError(f"Cannot load the shared replay driver from {DRIVER}")
    replay = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(replay)
    return replay


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="Pinned upstream checkout with prebuilt Lean imports")
    parser.add_argument("modules", nargs="*", help="Defaults to " + " and ".join(DEFAULT_TARGETS))
    parser.add_argument("--toolchain", type=Path, help="Path to the pinned Lean 4.36.0 installation",
                        default=Path.home() / ".elan/toolchains/leanprover--lean4---v4.36.0")
    args = parser.parse_intermixed_args(argv)
    targets = args.modules or DEFAULT_TARGETS
    replay = load_driver()
    checkout = args.checkout.resolve()
    toolchain = args.toolchain.resolve()
    revision = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    if revision != replay.REVISION or (checkout / "lean/lean-toolchain").read_text().strip() != replay.PIN:
        parser.error("checkout or Lean toolchain pin differs")
    lake = checkout / "lean/.lake"
    libs = [lake / "build/lib/lean", *sorted((lake / "packages").glob("*/.lake/build/lib/lean"))]
    if not (libs[0] / "PEqualNP").is_dir():
        parser.error("the pinned upstream Lean imports must already be built")
    sandbox = Path("/usr/bin/sandbox-exec")
    if not sandbox.exists():
        parser.error("this replay driver uses the macOS sandbox")
    cases = MATCH_CASES | replay.CASE_MODULES
    plan = replay.dependencies(targets)
    with tempfile.TemporaryDirectory(prefix="three-matching-replay-", dir="/private/tmp") as tmp:
        scratch = Path(tmp).resolve()
        env = {"HOME": str(scratch), "TMPDIR": str(scratch), "PATH": str(toolchain / "bin"),
               "LEAN_PATH": os.pathsep.join(map(str, [scratch, *libs])), "LEAN_NUM_THREADS": "1"}
        policy = scratch / "proof.sb"
        policy.write_text(replay.profile(scratch, libs, toolchain))

        def run(program, arguments, **kwargs):
            return subprocess.run([sandbox, "-f", policy, toolchain / "bin" / program, *arguments],
                                  cwd=scratch, env=env, check=True, **kwargs)

        version = run("lean", ["--version"], capture_output=True, text=True).stdout.strip()
        if not version.startswith("Lean (version 4.36.0,"):
            parser.error(f"unexpected Lean version: {version}")
        print(version, flush=True)
        cert_dir = scratch / "certificates"
        cert_dir.mkdir()
        for name, path in plan:
            print(f"Building {name}", flush=True)
            staged = scratch / path.name
            shutil.copyfile(path, staged)
            if name in cases:
                cert = path.parent / "certificates" / (name + ".lrat")
                shutil.copyfile(cert, cert_dir / cert.name)
            limits = ["-s", "131072", "-M", "5500"] if name in MATCH_CASES else []
            run("lean", [*limits, "-DwarningAsError=true", "-R", scratch, "-o", scratch / (name + ".olean"), staged])
        cert_modules = [name for name, _ in plan if name in cases]
        for name in dict.fromkeys([*cert_modules, *targets]):
            run("leanchecker", ["-v", name])
        print(f"Verified {', '.join(targets)} at {revision}.", flush=True)


if __name__ == "__main__":
    main()
