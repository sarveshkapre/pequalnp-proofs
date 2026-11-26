"""Recheck the published survivors using the independent signed-word search."""
from collections import Counter
import csv
from pathlib import Path

from check_vertex_mixed import check
from recheck_mixed_survivors import fano_control


def main():
    root = Path(__file__).resolve().parent
    fano_control()
    seen = set()
    by_stratum = Counter()
    totals = Counter()
    for line in (root / "survivors.txt").read_text().splitlines():
        if line.startswith("#"):
            continue
        stratum, index, *faces = map(int, line.split())
        assert (stratum, index) not in seen
        seen.add((stratum, index))
        assert len(set(faces)) == len(faces) == 13
        _, counts = check(faces)
        assert counts["designs"] > 0 and counts.get("two_sided", 0) == 0
        totals.update(counts)
        by_stratum[stratum] += 1
    with (root / "expected.tsv").open() as f:
        for row in csv.DictReader(f, delimiter="\t"):
            assert by_stratum[int(row["nonvertex_faces"])] == int(row["surviving_orbits"])
    assert len(seen) == 194 and totals["designs"] == 478
    assert totals["column_antichain"] == 85 and totals["two_sided"] == 0
    print(f"{len(seen)} surviving families:", dict(totals), "two-sided solutions: 0")


if __name__ == "__main__":
    main()
