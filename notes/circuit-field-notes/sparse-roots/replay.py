"""Check the upper-bound source, its public statement, and its compiled proof."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


PINNED_LOCK = "d0af863cde532caaef1b1bee0d63ec47100208e33e488309cb80abc88b8f1509"
PINNED_PROOF = "1f89014c6c765f1dd71294f770a21d36dab05fbbfec83614af9cc19c1b678a53"
AXIOM_REPORT = "'GapAudit.positive_root_count' depends on axioms: [propext, Classical.choice, Quot.sound]"


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("project", type=Path, help="prepared upstream lean/ directory")
    cli.add_argument("toolchain", type=Path, help="Lean 4.36.0 installation containing bin/")
    args = cli.parse_args()
    project = args.project.resolve()
    binary_dir = args.toolchain.resolve() / "bin"
    source_dir = Path(__file__).resolve().parent
    proof = source_dir / "EightPositiveRoots.lean"
    lock = (project / "lake-manifest.json").read_bytes()
    if hashlib.sha256(lock).hexdigest() != PINNED_LOCK:
        cli.error("The dependency lock differs from the one used for this proof.")
    if hashlib.sha256(proof.read_bytes()).hexdigest() != PINNED_PROOF:
        cli.error("The upper-bound proof differs from the checked release.")
    if "version 4.36.0," not in subprocess.check_output([binary_dir / "lean", "--version"], text=True):
        cli.error("Use Lean 4.36.0.")
    libraries = []
    for dep in json.loads(lock)["packages"]:
        root = project / ".lake/packages" / dep["name"]
        revision = subprocess.check_output(["git", "-C", root, "rev-parse", "HEAD"], text=True).strip()
        if revision != dep["rev"]:
            cli.error(f"Expected pinned revision for {dep['name']}.")
        library = root / ".lake/build/lib/lean"
        if library.is_dir():
            libraries.append(library)
    if not any((p / "Mathlib.olean").is_file() for p in libraries):
        cli.error("Build Mathlib or obtain its matching cache first.")
    with tempfile.TemporaryDirectory(prefix="sparse-roots-") as temp:
        build = Path(temp)
        shutil.copyfile(proof, build / proof.name)
        shutil.copyfile(source_dir / "CheckStatement.lean", build / "CheckStatement.lean")
        # leanchecker invokes lean by name, so both processes must use this installation.
        env = dict(os.environ, PATH=os.pathsep.join([str(binary_dir), os.environ.get("PATH", "")]),
                   LEAN_PATH=os.pathsep.join(map(str, [build, *libraries])))
        def run(command):
            result = subprocess.run(command, cwd=build, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                raise SystemExit(result.stdout)
            return result.stdout
        print("Checking the upper bound from source …", flush=True)
        run([binary_dir / "lean", "-t0", "-o", "EightPositiveRoots.olean", proof.name])
        print("Checking the imported root-count statement …", flush=True)
        if AXIOM_REPORT not in run([binary_dir / "lean", "-t0", "CheckStatement.lean"]).splitlines():
            raise SystemExit("Unexpected axioms for the public root-count theorem.")
        print("Replaying the compiled module …", flush=True)
        run([binary_dir / "leanchecker", "EightPositiveRoots"])
        print("PASS: source, imported statement, axiom report, and kernel replay.")


if __name__ == "__main__":
    main()
