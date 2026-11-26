"""Check the quadrangle proof with the checkout's pinned Lean and Mathlib."""

import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ATLAS = HERE.parent
PROJECT = ATLAS.parents[1] / "lean"
PACKAGES = PROJECT / ".lake" / "packages"
MATHLIB = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Build dependencies before their importers. Six sources already live on the
# contributor and sharing branches from which this branch descends.
MODULES = [
    (ATLAS, "TwoIntersections"),
    (ATLAS, "QuadrangleHandoff"),
    (HERE, "PartialRectangleColoring"),
    (ATLAS / "three-intersection-sharing", "ThreeIntersections"),
    (ATLAS / "three-intersection-sharing", "ThreeIntersectionsQuadrangle"),
    (HERE, "QuadranglePadding"),
    (ATLAS / "three-intersection-sharing", "ThreeIntersectionsSharingGap"),
    (HERE, "QuadrangleFormulaForests"),
    (HERE, "QuadranglePartialFooling"),
    (HERE, "QuadrangleSquareObstruction"),
    (HERE, "ThreeIntersectionsRepresentation"),
    (ATLAS / "three-intersection-sharing", "ThreeIntersectionsFormula"),
    (HERE, "QuadrangleFormulaCatalog"),
    (HERE, "QuadrangleSharedReduction"),
    (HERE, "QuadrangleBaseUnion"),
    (HERE, "QuadrangleFormulaExclusions"),
    (HERE, "QuadrangleSharedColoring"),
    (HERE, "QuadrangleSharedFinite"),
    (HERE, "QuadrangleSharedFiniteData"),
    (HERE, "QuadrangleStructural"),
]


def output(args, cwd, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    if result.returncode:
        sys.exit(result.stdout or f"{args[0]} exited with status {result.returncode}")
    return result.stdout


def check_reports(source, log):
    printed = re.findall(r"^#print axioms (\S+)", source, re.MULTILINE)
    seen = []
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        if used - ALLOWED_AXIOMS:
            sys.exit(f"Unexpected axioms for {name}: {used - ALLOWED_AXIOMS}")
        seen.append(name.rsplit(".", 1)[-1])
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        seen.append(name.rsplit(".", 1)[-1])
    if sorted(seen) != sorted(name.rsplit(".", 1)[-1] for name in printed):
        sys.exit("Axiom report names do not match the source declarations")
    return len(seen)


def main():
    version = output(["lean", "--version"], PROJECT).strip()
    if "version 4.36.0," not in version:
        sys.exit(f"Expected Lean 4.36.0, found {version}")
    revision = output(["git", "rev-parse", "HEAD"], PACKAGES / "mathlib").strip()
    if revision != MATHLIB:
        sys.exit(f"Expected Mathlib {MATHLIB}, found {revision}")
    binary = Path(output(["lean", "--print-prefix"], PROJECT).strip()) / "bin"
    libraries = sorted(PACKAGES.glob("*/.lake/build/lib/lean"))
    with TemporaryDirectory(prefix="quadrangle-structural-") as tmp:
        build = Path(tmp)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [build, *libraries])))
        reports = 0
        for directory, module in MODULES:
            filename = module + ".lean"
            source = build / filename
            shutil.copyfile(directory / filename, source)
            log = output([binary / "lean", "--root=.", "-o", module + ".olean", filename],
                         build, env)
            reports += check_reports(source.read_text(encoding="utf-8"), log)
            print(f"Built {module}", flush=True)
            print(log, end="")
        for _, module in MODULES:
            print(output([binary / "leanchecker", "-v", module], build, env), end="")
        print(f"Passed {len(MODULES)} source builds, {len(MODULES)} kernel checks "
              f"and {reports} axiom reports")


if __name__ == "__main__":
    main()
