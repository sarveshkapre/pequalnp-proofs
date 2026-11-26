"""Check every surviving row family in signed words, including a Fano control."""
import argparse
from collections import Counter
from pathlib import Path

from check_vertex_mixed import WORDS, check, compatible, has_two_sided, subset_face


def fano_control():
    row_masks = [42, 25, 76, 7, 82, 97, 52]
    point_labels = [12, 11, 10, 0, 15, 7, 5]
    line_labels = [12, 3, 15, 5, 6, 10, 9]
    vertex = [tuple((i >> j) & 1 for j in range(4)) for i in range(16)]
    hits = {w: sum(1 << i for i, v in enumerate(WORDS) if compatible(w, v)) for w in WORDS}
    forbidden = [sum(1 << i for i, v in enumerate(WORDS) if subset_face(w, v) or subset_face(v, w))
                 for w in WORDS]
    rows = [vertex[i] for i in point_labels]
    domains = [1 << WORDS.index(vertex[i]) for i in line_labels]
    blocks = [{p for p, mask in enumerate(row_masks) if mask >> col & 1} for col in range(7)]
    assert has_two_sided(rows, blocks, domains, hits, forbidden)
    assert not has_two_sided(rows, blocks, [domains[0]] * 7, hits, forbidden)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--through", type=int, choices=range(14), default=13)
    args = parser.parse_args()
    root = Path(__file__).parent
    fano_control()
    print("positive and negative Fano controls passed", flush=True)
    totals = Counter()
    for n in range(args.through + 1):
        first = (root / f"mixed-design-survivors-{n}.in").read_bytes()
        second = (root / f"pencil-survivors-{n}.in").read_bytes()
        assert first == second, n
        total = Counter()
        for raw in first.splitlines():
            index, *faces = map(int, raw.split())
            assert len(faces) == 13 and len(set(faces)) == 13
            _, count = check(faces)
            assert count["designs"] > 0 and count.get("two_sided", 0) == 0, (n, index, count)
            total.update(count)
            total["families"] += 1
            print(n, index, count, flush=True)
        totals.update(total)
        print("stratum", n, dict(total), flush=True)
    print("totals", dict(totals))


if __name__ == "__main__":
    main()
