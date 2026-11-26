"""Check the three operand lists and the published Fano weights using integers."""
from itertools import combinations, product
from pathlib import Path
import re


def check_operands(masks, point_labels, line_labels, digits, width):
    size = len(masks)
    flags = []
    zeros = []
    rows = [0] * size
    cols = [0] * size
    for p, row_mask in enumerate(masks):
        for line in range(size):
            if row_mask >> line & 1:
                flags.append((p, line))
                continue
            cell = 1 << (p * size + line)
            zeros.append((p, line, cell))
            rows[p] |= cell
            cols[line] |= cell

    signs = (1, 2) if digits == 3 else (0, 1)
    operands = []
    for i in range(width):
        place = digits ** i
        def arm(sign):
            return sum(cell for p, line, cell in zeros
                       if point_labels[p] // place % digits == sign
                       or line_labels[line] // place % digits == sign)
        operands.append((arm(signs[0]), arm(signs[1])))

    def covered(a, b):
        def belongs(s):
            return (s & a) == a or (s & b) == b
        return any(belongs(e) and belongs(h) and not belongs(e & h)
                   for e, h in operands)

    canonical = sum(covered(rows[p], cols[line]) for p, line in flags)
    row_tests = sum(covered(rows[p], z) for p, line in flags
                    for _, l, z in zeros if l == line)
    column_tests = sum(covered(cols[line], z) for p, line in flags
                       for r, _, z in zeros if r == p)
    return (canonical, row_tests, column_tests), covered, cols


def fano_weights():
    path = Path(__file__).parent / "lean" / "FusionFanoCertificateData.lean"
    triples = re.findall(r"^\s*\((\d+), (\d+), (\d+)\),?\s*$",
                         path.read_text(), re.MULTILINE)
    # Lean uses a wildcard 0, with signs 1 and 2. The code is in base three.
    words = list(product(range(3), repeat=3))
    def refines(a, b):
        return all(y == 0 or x == y for x, y in zip(a, b))
    def compatible(a, b):
        return all(x == 0 or y == 0 or x == y for x, y in zip(a, b))
    hits = [sum(1 << i for i, w in enumerate(words) if compatible(v, w)) for v in words]

    def antichains(prefix, candidates):
        if len(prefix) == 7:
            yield tuple(prefix)
            return
        for i, v in enumerate(candidates):
            if len(candidates) - i < 7 - len(prefix):
                return
            rest = [w for w in candidates[i+1:]
                    if not refines(words[v], words[w]) and not refines(words[w], words[v])]
            yield from antichains(prefix+[v], rest)

    required = set(antichains([], list(range(27))))
    assert len(triples) == len(required) == 2260
    edges = list(combinations(range(7), 2))
    eligible = 0
    for encoded, positive, negative in triples:
        code, pos, neg = map(int, (encoded, positive, negative))
        rows = tuple(code // (27 ** i) % 27 for i in range(7))
        required.remove(rows)
        assert not pos & neg
        weights = {pair: ((pos >> i) & 1) - ((neg >> i) & 1)
                   for i, pair in enumerate(edges)}
        assert sum(weights.values()) == 1
        for block in combinations(range(7), 3):
            safe = (1 << 27) - 1
            for p in block:
                safe &= ~hits[rows[p]]
            outside = [rows[p] for p in range(7) if p not in block]
            if any(safe >> c & 1 and all(safe & hits[c] & hits[r] for r in outside)
                   for c in range(27)):
                assert sum(weights[e] for e in combinations(block, 2)) <= 0
                eligible += 1
    assert not required and eligible == 30548
    print("Fano weight certificates:", len(triples), "row families,", eligible, "eligible triples")


if __name__ == "__main__":
    fano = [42,25,76,7,82,97,52]
    pg3 = [1170,113,2584,4372,15,4674,2338,7169,1352,1572,897,2244,4264]
    four, _, _ = check_operands(fano, [12,11,10,0,15,7,5], [12,3,15,5,6,10,9], 2, 4)
    assert four == (21, 84, 84)
    one, covered, cols = check_operands(pg3, [49,76,43,53,70,77,68,41,44,79,50,71,80],
                                       [24,24,3,3,11,27,28,10,1,63,57,18,1], 3, 4)
    assert one == (52, 468, 406) and not covered(cols[1], 1)
    both, _, _ = check_operands(pg3, [6,18,24,17,15,9,30,10,0,23,29,3,5],
                                [4,16,28,19,13,8,31,26,11,2,25,21,22], 2, 5)
    assert both == (52, 468, 468)
    print("Passing canonical, row and column tests:", four, one, both)
    fano_weights()
