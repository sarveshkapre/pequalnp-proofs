"""Check the ten Lean statements using a disposable checkout of the pinned project."""

import argparse
from pathlib import Path
import subprocess


REVISION = "e6bfe1a56efc768d244627b78f175b18de1acd6f"
MODULES = (
    "TightFamily", "FormulaGap", "TwinReduction", "TwinTable", "TwinDeskBatch",
    "CircuitCopies", "OriginalCopyFamily", "CopyDeskCensus", "MissingMatching", "ThreeMissing",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="local path to a prepared upstream checkout")
    tree = parser.parse_args().checkout.resolve()
    package = Path(__file__).resolve().parent
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=tree, text=True).strip()
    if revision != REVISION:
        parser.error(f"expected upstream revision {REVISION}")

    outside = tree / "lean/PEqualNP/Outside"
    for name in MODULES:
        source = (package / "proofs" / f"{name}.lean").read_bytes()
        target = outside / f"{name}.lean"
        if target.exists():
            if target.read_bytes() != source:
                parser.error(f"{target.name} already exists with different contents")
        else:
            target.write_bytes(source)

    for name in MODULES:
        subprocess.run(
            ["node", "tools/check-lean.mjs", f"lean/PEqualNP/Outside/{name}.lean",
             str(package / "statements" / f"{name}.statement"), "check"],
            cwd=tree, check=True,
        )


if __name__ == "__main__":
    main()
