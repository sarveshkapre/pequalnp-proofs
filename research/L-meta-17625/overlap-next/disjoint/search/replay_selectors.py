"""Rebuild the finite selector exclusion using an installed Lean 4.36.0 and mathlib cache."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import os
from pathlib import Path
import subprocess
import tempfile

SOURCE = Path(__file__).resolve().parent
MODES = ("Outside", "Inside", "Cross")
ORDERS = ("AAOO", "AOAO", "AOOA", "OAAO", "OAOA", "OOAA")
CASES = tuple("Projection" + mode + order for mode in MODES for order in ORDERS)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lean_bin", type=Path, help="bin directory of the pinned Lean installation")
    parser.add_argument("packages", type=Path, help="prepared project lean/.lake/packages directory")
    parser.add_argument("--workers", type=int, choices=(1, 2), default=2)
    args = parser.parse_args()
    binaries = args.lean_bin.resolve()
    packages = args.packages.resolve()
    libraries = sorted(packages.glob("*/.lake/build/lib/lean"))
    if not (packages / "mathlib/.lake/build/lib/lean/Mathlib/Tactic/Sat/FromLRAT.olean").is_file():
        parser.error("missing mathlib LRAT proof-producing tactic in the supplied package cache")

    manifest = {}
    for line in (SOURCE / "certificates.sha256").read_text().splitlines():
        digest, path = line.split("  ", 1)
        manifest[path] = digest
    if set(manifest) != {"certificates/" + m + ".lrat" for m in CASES}:
        parser.error("the manifest must describe exactly the eighteen selector certificates")
    for path, digest in manifest.items():
        if sha256((SOURCE / path).read_bytes()).hexdigest() != digest:
            parser.error("certificate checksum mismatch for " + path)

    with tempfile.TemporaryDirectory(prefix="disjoint-selector-replay-") as dest:
        out = Path(dest)
        env = {
            "PATH": os.pathsep.join((str(binaries), "/usr/bin", "/bin")),
            "TMPDIR": str(out),
            "LEAN_PATH": os.pathsep.join([str(out)] + [str(lib) for lib in libraries]),
            "LEAN_NUM_THREADS": "1",
        }
        version = subprocess.check_output([binaries / "lean", "--version"], env=env, text=True)
        if "version 4.36.0," not in version:
            parser.error("expected Lean 4.36.0, found " + version.strip())
        print(version.strip(), flush=True)

        def build(module):
            result = subprocess.run(
                [binaries / "lean", "-s", "131072", "-DwarningAsError=true", "-R", SOURCE,
                 "-o", out / (module + ".olean"), SOURCE / (module + ".lean")],
                env=env, cwd=out, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if result.returncode:
                raise RuntimeError(module + " failed\n" + result.stdout)
            print(result.stdout.rstrip() or ("Built " + module), flush=True)

        for module in ("ProjectedSchedule", "SelectorBits", "KernelProp"):
            build(module)
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            list(pool.map(build, CASES))
        build("ProjectionExclusion")
        subprocess.run([binaries / "leanchecker", "-v", "ProjectionExclusion"],
                       cwd=out, env=env, check=True)
        print("Rebuilt all eighteen selector proofs and replayed ProjectionExclusion.", flush=True)


if __name__ == "__main__":
    main()
