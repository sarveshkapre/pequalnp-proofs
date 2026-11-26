"""Rebuild the local Lean sources from a pinned, prebuilt checkout on macOS.

No fetches, Lake project scripts, or user shell initialization are run. Lean and
its kernel checker see only staged research, the prebuilt imports, the toolchain,
and operating-system libraries. Outputs can be reproduced without GitHub access.
"""
import argparse
import json
import os
import shutil
import subprocess
import tempfile
from graphlib import TopologicalSorter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REVISION = "e6bfe1a56efc768d244627b78f175b18de1acd6f"
PIN = "leanprover/lean4:v4.36.0"
CASE_MODULES = {f"Projection{mode}{order}" for mode in ("Outside", "Inside", "Cross")
                for order in ("AAOO", "AOAO", "AOOA", "OAAO", "OAOA", "OOAA")}


def dependencies(targets):
    paths = {}
    for path in sorted(HERE.parent.parent.rglob("*.lean")):
        if path.stem in paths:
            raise ValueError(f"duplicate Lean module {path.stem}: {path}")
        paths[path.stem] = path
    graph = {}
    pending = list(targets)
    while pending:
        name = pending.pop()
        if name in graph:
            continue
        imported = set()
        for line in paths[name].read_text().splitlines():
            if line.startswith(("import ", "public import ")):
                imported.update(line.split("import ", 1)[1].split())
        graph[name] = sorted(imported & paths.keys())
        pending.extend(graph[name])
    return [(m, paths[m]) for m in TopologicalSorter(graph).static_order()]


def profile(scratch, libs, toolchain):
    reads = [scratch, *libs, toolchain, Path("/System/Library"), Path("/usr/lib"),
             Path("/usr/share"), Path("/Library/Apple")]
    return "\n".join((
        '(version 1)', '(deny default)', '(import "dyld-support.sb")',
        '(allow sysctl-read)', '(allow file-read-metadata)', '(allow signal (target self))',
        '(allow process-fork)', '(allow process-exec (subpath ' + json.dumps(str(toolchain / "bin")) + '))',
        '(allow file-read* (literal "/") (literal "/dev/null") (literal "/dev/random") (literal "/dev/urandom") '
        + " ".join("(subpath " + json.dumps(str(p)) + ")" for p in reads) + ")",
        '(allow file-map-executable (subpath ' + json.dumps(str(toolchain)) + ') (subpath "/System/Library") (subpath "/usr/lib"))',
        '(allow file-write* (subpath ' + json.dumps(str(scratch)) + ') (literal "/dev/null"))',
    ))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("modules", nargs="*", default=["TwoTouching"])
    parser.add_argument("--toolchain", type=Path,
                        default=Path.home() / ".elan/toolchains/leanprover--lean4---v4.36.0")
    options = parser.parse_args()
    checkout = options.checkout.resolve()
    toolchain = options.toolchain.resolve()
    revision = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    if revision != REVISION or (checkout / "lean/lean-toolchain").read_text().strip() != PIN:
        parser.error("checkout or Lean toolchain pin differs")
    lake = checkout / "lean/.lake"
    libs = [lake / "build/lib/lean", *sorted((lake / "packages").glob("*/.lake/build/lib/lean"))]
    if not (libs[0] / "PEqualNP").is_dir():
        parser.error("the pinned upstream Lean imports must already be built")
    sandbox = Path("/usr/bin/sandbox-exec")
    if not sandbox.exists():
        parser.error("this replay driver uses the macOS sandbox")
    plan = dependencies(options.modules)
    with tempfile.TemporaryDirectory(prefix="three-edge-replay-", dir="/private/tmp") as tmp:
        scratch = Path(tmp).resolve()
        env = {"HOME": str(scratch), "TMPDIR": str(scratch), "PATH": str(toolchain / "bin"),
               "LEAN_PATH": os.pathsep.join(map(str, [scratch, *libs])), "LEAN_NUM_THREADS": "1"}
        policy = scratch / "proof.sb"
        policy.write_text(profile(scratch, libs, toolchain))
        def run(program, args, **kwargs):
            return subprocess.run([sandbox, "-f", policy, toolchain / "bin" / program, *args],
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
            if name in CASE_MODULES:
                cert = path.parent / "certificates" / (name + ".lrat")
                shutil.copyfile(cert, cert_dir / cert.name)
            run("lean", ["-DwarningAsError=true", "-R", scratch, "-o", scratch / (name + ".olean"), staged])
        replay = [name for name, _ in plan if name in CASE_MODULES]
        for name in dict.fromkeys([*replay, *options.modules]):
            run("leanchecker", ["-v", name])
        print(f"Verified {', '.join(options.modules)} at {revision}.", flush=True)


if __name__ == "__main__":
    main()
