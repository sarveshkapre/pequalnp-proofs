"""Build the circuit lemmas and replay the six-edge certificate table offline."""

import argparse
from graphlib import TopologicalSorter
import os
from pathlib import Path
import shutil
from subprocess import check_output, run
import sys
from tempfile import TemporaryDirectory


SOURCE = Path(__file__).resolve().parent
REVISION = "e6bfe1a56efc768d244627b78f175b18de1acd6f"


def imports(path):
    for line in path.read_text().splitlines():
        if line.startswith("import "):
            yield from line.split()[1:]


def verify(checkout, lean, jobs, proof_only, kernel_replay):
    revision = check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
    if revision != REVISION:
        raise ValueError(f"Expected the pinned upstream revision {REVISION}, found {revision}.")
    upstream = checkout / "lean"
    cached = upstream / ".lake" / "build" / "lib" / "lean"
    packages = sorted(upstream.glob(".lake/packages/*/.lake/build/lib/lean"))
    own = {f.stem: f for f in SOURCE.glob("*.lean")}
    neighbours = {f.stem: f for f in (SOURCE.parent / "overlap").glob("*/*.lean")}
    local = neighbours | own

    with TemporaryDirectory(prefix="six-edge-check-") as directory:
        out = Path(directory)
        # Lean resolves a module under the first root containing its package.
        # Make the cached modules visible from the temporary package root.
        shutil.copytree(cached / "PEqualNP", out / "PEqualNP", copy_function=os.symlink)
        env = os.environ | {
            "LEAN_PATH": os.pathsep.join(map(str, [out, *packages])),
            "PATH": os.pathsep.join([str(lean.parent), os.environ.get("PATH", "")]),
        }
        sources = {}
        dependencies = {}
        pending = list(own)
        while pending:
            name = pending.pop()
            if name in sources:
                continue
            if name in local:
                path = local[name]
            elif name.startswith("PEqualNP."):
                relative = Path(*name.split(".")).with_suffix(".lean")
                if (out / relative.with_suffix(".olean")).is_file():
                    continue
                path = upstream / relative
                body = path.read_bytes()
                pinned = check_output(["git", "show", f"{REVISION}:lean/{relative.as_posix()}"], cwd=checkout)
                if body != pinned or any(flag in body for flag in
                    (b"run_tac", b"#eval", b"run_cmd", b"native_decide", b"unsafe", b"IO.")):
                    raise ValueError(f"Upstream source needs review before compilation: {relative}")
            else:
                continue
            sources[name] = path
            required = set(imports(path))
            dependencies[name] = required
            pending.extend(required)

        build = {name: required & sources.keys() for name, required in dependencies.items()}
        for name in TopologicalSorter(build).static_order():
            path = sources[name]
            root = upstream if name.startswith("PEqualNP.") else path.parent
            target = out / Path(*name.split(".")).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            print(f"Checking {name}", flush=True)
            run([lean, f"--root={root}", "-o", target, path], env=env, check=True)
        if kernel_replay:
            for name in own:
                print(f"Replaying {name} in the standalone kernel", flush=True)
                run([lean.with_name("leanchecker"), name], env=env, check=True)
        if not proof_only:
            run([sys.executable, "-B", SOURCE / "replay.py", "--lean", lean,
                 "--cadical", lean.with_name("cadical"), "--jobs", str(jobs)], env=env, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--proof-only", action="store_true")
    parser.add_argument("--kernel-replay", action="store_true")
    args = parser.parse_args()
    verify(args.checkout.resolve(), args.lean.absolute(), args.jobs, args.proof_only, args.kernel_replay)


if __name__ == "__main__":
    main()
