"""Compile the finite certificates and replay each module with Lean's kernel checker."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
PIN = "e6bfe1a56efc768d244627b78f175b18de1acd6f"
MODULES = [
    "mask-69/Refutation.lean", "mask-69/SevenGates.lean", "mask-69/SixPoints.lean",
    "rectangle-cover/Desk9348Partial.lean", "rectangle-cover/Desk9348Rearranged.lean",
    "rectangle-cover/symmetry/SymmetricPlane.lean", "rectangle-cover/symmetry/TwoUnmatched.lean",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="Prebuilt upstream pequalnp-proofs checkout")
    parser.add_argument("lean_bin", type=Path, help="Lean 4.36.0 bin directory")
    parser.add_argument("--fresh", action="store_true", help="Also recheck all imported declarations for each module")
    args = parser.parse_args()
    repo = args.checkout.resolve()
    tools = args.lean_bin.resolve()
    head = subprocess.check_output(["git", "-C", repo, "rev-parse", "HEAD"], text=True).strip()
    version = subprocess.check_output([tools / "lean", "--version"], text=True)
    if head != PIN or not version.startswith("Lean (version 4.36.0,"):
        parser.error("Use the upstream revision and Lean version in the README.")
    lake = repo / "lean/.lake"
    base = lake / "build/lib/lean"
    if not (base / "PEqualNP/Defs.olean").is_file():
        parser.error("Build PEqualNP.Defs in the upstream checkout first.")
    libs = [base, *sorted((lake / "packages").glob("*/.lake/build/lib/lean"))]
    with tempfile.TemporaryDirectory(prefix="finite-certificate-") as temporary:
        scratch = Path(temporary)
        env = {**os.environ, "LEAN_PATH": os.pathsep.join(map(str, [scratch, *libs]))}
        for entry in MODULES:
            src = ROOT / entry
            shutil.copyfile(src, scratch / src.name)
            subprocess.run([tools / "lean", "-s", "65536", "-o", src.stem + ".olean", src.name],
                           cwd=scratch, env=env, check=True)
            checker_args = [tools / "leanchecker"]
            if args.fresh:
                checker_args.append("--fresh")
            subprocess.run([*checker_args, src.stem], cwd=scratch, env=env, check=True)
            print(f"{src.stem} passed its kernel replay.", flush=True)


if __name__ == "__main__":
    main()
