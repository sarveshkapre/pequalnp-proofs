"""Check that the two certificate formulas cover every choice of three rows."""

from collections import Counter
import hashlib
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory

from triple_line import GRID, ROWS, instance, project
from cases import allowed, cases, verify
import sys

sys.path.insert(0, str(GRID / "bounds"))
from clean_grid import row_stars

FORMULAS = {
    9: "eed3a00fe4dc8c1541451cadbce2dd73e45ed850248351ea49dc651d70d5b9e1",
    10: "3d412f81d9c6bd1786902d0f2417017e1256a0ab24d10ee018859e1287ce3dff",
}


def main():
    counts = Counter()
    with TemporaryDirectory() as directory:
        path = Path(directory) / "projection.cnf"
        for triple in combinations(range(6), 3):
            free, targets, lines = project(triple, "universal")
            instance(path, free, targets, len(lines), 8)
            assert hashlib.sha256(path.read_bytes()).hexdigest() == FORMULAS[len(lines)]
            for i in triple:
                for j in lines:
                    target_bit = bool(ROWS[i] & (1 << j))
                    assert allowed(1 << i, 1 << j) == (not target_bit)
            counts[len(lines)] += 1
    assert counts == {9: 18, 10: 2}
    print("All 20 triples map exactly to the two certified formulas (2 concurrent and 18 triangular).")
    print("Every projected off-row singleton is a legal negative.")

    circuit, output = row_stars()
    assert len(circuit) == 29 and output == 58
    assert len(cases()) == 177 and verify(circuit) == []
    print("Ordinary three-OR trees use nine line gates for any triple and pass the full test set.")


if __name__ == "__main__":
    main()
