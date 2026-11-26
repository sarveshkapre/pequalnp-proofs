"""Encode a symmetric twelve-rectangle core and two freely chosen rectangles."""
import argparse
from itertools import combinations
from pathlib import Path

from symmetric import CNF, POINTS, POLARITY, board


def encode(k, pole_case=None, anchor=None, small=False, control=False):
    rows, allowed, original_pairs, original_squares = board()
    boundary = [p for p in POINTS if not allowed[p][p]]
    pole, = [p for p in POINTS if p not in boundary and not any(allowed[p][a] for a in boundary)]
    forbidden = [[q for q in POINTS if not allowed[p][q]] for p in POINTS]
    f = CNF()
    clauses = f.clauses

    def side(mask):
        return [f.var(mask >> p & 1) for p in POINTS]

    pairs = [(side(a), side(b)) for a, b in (original_pairs + [(0, 0)] * 6)[:k]]
    squares = [side(a) for a in (original_squares + [0] * 12)[:12 - 2 * k]]
    a, b = original_pairs[k] if k < len(original_pairs) else (0, 0)
    x, y, u, v = map(side, (a & b, a & b, a, b))

    def legal(left, right):
        for i in POINTS:
            clauses.extend([[-left[i], -right[j]] for j in forbidden[i]])

    def maximal_pair(left, right, neighbors):
        for first, second in [(left, right), (right, left)]:
            for i in POINTS:
                clauses.append([first[i]] + [s[j] for s in [second] + neighbors for j in forbidden[i]])

    def maximal_square(s, neighbors):
        for i in POINTS:
            if i in boundary:
                clauses.append([-s[i]])
                continue
            inside = [j for j in forbidden[i] if j not in boundary]
            clauses.extend([[-s[i], -s[j]] for j in inside if j < i])
            clauses.append([s[i]] + [s[j] for j in inside] +
                           [other[j] for other in neighbors for j in forbidden[i]])

    for left, right in pairs:
        legal(left, right)
        maximal_pair(left, right, [])
    for s in squares:
        maximal_square(s, [])
    for s in [x, y]:
        maximal_square(s, [u, v])
        legal(s, u)
        legal(s, v)
    legal(u, v)
    maximal_pair(u, v, [x, y])

    pinned = {}

    def pin(var, value):
        pinned[var] = value
        clauses.append([var if value else -var])

    if pole_case is not None:
        both, one, special = pole_case
        for i, (left, right) in enumerate(pairs):
            pin(left[pole], i < both + one)
            pin(right[pole], i < both)
        pin(u[pole], special >= 1)
        pin(v[pole], special == 2)

    if anchor:
        left_size, right_size = anchor
        first_cut = pairs[both + one]
        for s, members in zip(first_cut, (boundary[:left_size], boundary[left_size:left_size + right_size])):
            for p in boundary:
                pin(s[p], p in members)

    def pin_pattern(s):
        return tuple(pinned.get(s[p]) for p in [pole] + boundary)

    def trace(s):
        return [s[p] for p in boundary]

    # The same row-major lexicographic maximum satisfies the slot and column orders.
    for i, (left, right) in enumerate(pairs):
        if pin_pattern(left) == pin_pattern(right):
            f.lex(trace(left) + trace(right), trace(right) + trace(left))
        for c, d in pairs[i + 1:]:
            for h, j in [(c, d), (d, c)]:
                if (pin_pattern(left), pin_pattern(right)) == (pin_pattern(h), pin_pattern(j)):
                    f.lex(trace(left) + trace(right), trace(h) + trace(j))
    if pin_pattern(u) == pin_pattern(v):
        f.lex(trace(u) + trace(v), trace(v) + trace(u))
    groups = {}
    for p in boundary:
        key = tuple(pinned[s[p]] for s in first_cut) if anchor else ()
        groups.setdefault(key, []).append(p)
    # The control deliberately omits two *named* diagonal cells. Their names
    # break the full boundary relabeling symmetry of the actual problem.
    for group in ([] if control else groups.values()):
        for i, j in zip(group, group[1:]):
            f.lex([s[i] for pair in pairs + [(u, v)] for s in pair],
                  [s[j] for pair in pairs + [(u, v)] for s in pair])
    for first, second in zip(squares, squares[1:]):
        f.lex(first, second)
    f.lex(x, y)

    if not control:
        # Otherwise the two unmatched slots can be replaced by two symmetric slots.
        clauses.append([f.both(x[i], y[j]) for i in POINTS if i not in boundary
                        for j in forbidden[i] if j not in boundary])
        clauses.append([f.both(s[i], s[j]) for s in [u, v] for i in POINTS
                        for j in forbidden[i] if j <= i])

    for i in POINTS:
        for j in range(i, len(POINTS)):
            if not allowed[i][j] or (control and i == j and i in (6, 10)):
                continue
            choices = [f.both(left[i], right[j]) for left, right in pairs + [(u, v)]]
            if i != j:
                choices.extend(f.both(left[j], right[i]) for left, right in pairs + [(u, v)])
            if i not in boundary and j not in boundary:
                choices.extend(f.both(s[i], s[j]) for s in squares + [x, y])
            clauses.append(choices)
    if small:
        for pair in pairs[both + one:]:
            for s in pair:
                for three in combinations(boundary, 3):
                    clauses.append([-s[p] for p in three])
    if control:
        if k != 5 or pole_case or anchor or small:
            raise ValueError('the 334-cell control uses the original five pairs plus two free slots')
        def signature(mask, pts):
            return tuple(mask >> p & 1 for p in pts)

        def orient(pair):
            return sorted(pair, key=lambda m: signature(m, boundary), reverse=True)

        def pin_mask(variables, mask):
            for p in POINTS:
                pin(variables[p], bool(mask >> p & 1))

        ordered = sorted(map(orient, original_pairs[:k]),
                         key=lambda pair: tuple(signature(m, boundary) for m in pair), reverse=True)
        for variables, masks in zip(pairs, ordered):
            for s, m in zip(variables, masks):
                pin_mask(s, m)
        for s, m in zip(squares, sorted(original_squares, key=lambda m: signature(m, POINTS), reverse=True)):
            pin_mask(s, m)
        for s, m in zip((u, v), orient(original_pairs[k])):
            pin_mask(s, m)
    return f, pairs, squares, (x, y, u, v), rows


def check_model(model, encoding, control):
    f, pairs, squares, special, rows = encoding
    assignment = {abs(v): v > 0 for line in model.read_text().splitlines() if line.startswith('v ')
                  for v in map(int, line.split()[1:]) if v}

    def mask(s):
        return sum((assignment[v] != f.signs[v]) << i for i, v in enumerate(s))

    pairs = [(mask(a), mask(b)) for a, b in pairs]
    x, y, u, v = map(mask, special)
    folded = pairs + [(b, a) for a, b in pairs] + [(mask(s), mask(s)) for s in squares]
    folded.extend([(x | u, x | v), (y | v, y | u)])
    boxes = [(a, sum((b >> p & 1) << col for p, col in enumerate(POLARITY))) for a, b in folded]
    assert len(boxes) == 14
    missed = []
    for i in POINTS:
        for j in POINTS:
            covered = any((a >> i) & (b >> j) & 1 for a, b in boxes)
            assert not (covered and rows[i] >> j & 1)
            if not covered and not (rows[i] >> j & 1):
                missed.append((i, j))
    assert not missed or (control and set(missed) <= {(6, 17), (10, 13)})
    print(f'{336 - len(missed)} of 336 cells covered, all 441 cells checked.')
    return boxes


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cnf', type=Path)
    parser.add_argument('pairs', type=int, choices=range(7))
    parser.add_argument('--pole', type=int, nargs=3, metavar=('BOTH', 'ONE', 'SPECIAL'))
    parser.add_argument('--anchor', type=int, nargs=2, metavar=('LEFT', 'RIGHT'))
    parser.add_argument('--small', action='store_true', help='at most two boundary points on either ordinary cut side')
    parser.add_argument('--control', action='store_true', help='allow the two holes in the symmetric witness')
    parser.add_argument('--model', type=Path, help='score a solver model on the original board')
    args = parser.parse_args()
    if args.pole and (min(args.pole) < 0 or sum(args.pole[:2]) > args.pairs or args.pole[2] > 2):
        parser.error('invalid pole counts')
    if args.anchor and (not args.pole or sum(args.pole[:2]) >= args.pairs or
                        min(args.anchor) < 1 or sum(args.anchor) > 5):
        parser.error('an anchor requires a free two-sided ordinary cut')
    if args.small and not args.pole:
        parser.error('small cuts require a pole split')
    result = encode(args.pairs, args.pole, args.anchor, args.small, args.control)
    result[0].save(args.cnf)
    if args.model:
        check_model(args.model, result, args.control)
