"""Encode covers made of self-transpose rectangles and transposed pairs."""
import argparse
from itertools import combinations
from pathlib import Path
import re


POLARITY = [2, 3, 7, 0, 8, 14, 17, 1, 9, 4, 13, 19, 11, 15, 10, 12, 20, 6, 5, 18, 16]
POINTS = range(21)
SOURCE = Path(__file__).resolve().parents[1] / 'Desk9348Partial.lean'


def board():
    source = SOURCE.read_text()
    rows = list(map(int, re.search(r'def rows : List Nat := \[([^\]]+)\]', source)[1].split(',')))
    data = source.split('def rectangles : List (Nat × Nat) := [')[1].split(']')[0]
    seed = [(int(x), int(y)) for x, y in re.findall(r'\((\d+), (\d+)\)', data)]
    transpose = lambda cols: sum((cols >> col & 1) << i for i, col in enumerate(POLARITY))
    allowed = [[not bool(rows[p] >> POLARITY[q] & 1) for q in POINTS] for p in POINTS]
    assert len(rows) == 21 and len(seed) == 14 and len(set(POLARITY)) == 21
    assert all(allowed[p][q] == allowed[q][p] for p in POINTS for q in POINTS)
    pairs = [(x, transpose(y)) for x, y in seed]
    assert all((y, x) in pairs for x, y in pairs)
    return rows, allowed, sorted((x, y) for x, y in pairs if x < y), [x for x, y in pairs if x == y]


class CNF:
    def __init__(self):
        self.signs = [False]
        self.clauses = []

    def var(self, initial=False):
        self.signs.append(bool(initial))
        return len(self.signs) - 1

    def both(self, a, b):
        if a == b:
            return a
        v = self.var(self.signs[a] and self.signs[b])
        self.clauses.extend([[-v, a], [-v, b], [v, -a, -b]])
        return v

    def lex(self, left, right):
        # Require left >= right at the first differing bit. Equal prefixes
        # force the continuation variable, so no reverse implication is needed.
        eq = None
        for x, y in zip(left, right):
            if x == y:
                continue
            prefix = [] if eq is None else [-eq]
            self.clauses.append(prefix + [x, -y])
            step = self.var((eq is None or self.signs[eq]) and self.signs[x] == self.signs[y])
            self.clauses.extend([prefix + [-x, -y, step], prefix + [x, y, step]])
            eq = step

    def save(self, path):
        with path.open('w') as out:
            print('p cnf', len(self.signs) - 1, len(self.clauses), file=out)
            for clause in self.clauses:
                print(*[-x if self.signs[abs(x)] else x for x in clause], 0, file=out)


def make(args):
    rows, allowed, original, fixed = board()
    absolute = [p for p in POINTS if not allowed[p][p]]
    assert absolute == [2, 12, 14, 19, 20]
    pole, = [p for p in POINTS if p not in absolute and not any(allowed[p][a] for a in absolute)]
    frozen = [p for k, p in enumerate(absolute) if not (args.free >> k & 1)]
    f = CNF()
    bits = lambda mask: [f.var(mask >> p & 1) for p in POINTS]
    pairs = [(bits(x), bits(y)) for x, y in (original + [(0, 0)])[:args.pairs]]
    n_single = args.budget - 2 * args.pairs - args.unmatched
    if n_single < 0 or (args.unmatched and (args.pole or args.boundary_only)):
        raise ValueError('unsupported combination of rectangle budgets')
    singles = [bits(x) for x in (fixed + [0] * 14)[:n_single]]
    unpaired = []
    if args.unmatched:
        x, y = original[args.pairs] if args.pairs < len(original) else (0, 0)
        unpaired = [(bits(x), bits(y)), (bits(y), bits(x))]
        for a, b in unpaired:
            for p in POINTS:
                forbidden = [q for q in POINTS if not allowed[p][q]]
                f.clauses.extend([[-a[p], -b[q]] for q in forbidden])
                f.clauses.append([a[p]] + [b[q] for q in forbidden])
                f.clauses.append([b[p]] + [a[q] for q in forbidden])
    pinned = {}
    anchor = None
    if args.pole is not None:
        both, single = args.pole
        if frozen or min(both, single) < 0 or both + single > args.pairs:
            raise ValueError('pole split requires all five profiles free and feasible counts')
        for k, (a, b) in enumerate(pairs):
            for side, present in [(a, k < both + single), (b, k < both)]:
                pinned[side[pole]] = present
                f.clauses.append([side[pole] if present else -side[pole]])
        if args.anchor is not None:
            left, right = args.anchor
            if both + single >= args.pairs or min(left, right) < 1 or left + right > 5:
                raise ValueError('invalid boundary cut')
            anchor = pairs[both + single]
            for side, members in zip(anchor, (absolute[:left], absolute[left:left + right])):
                for p in absolute:
                    pinned[side[p]] = p in members
                    f.clauses.append([side[p] if p in members else -side[p]])
    elif args.anchor is not None:
        raise ValueError('an anchor requires a pole split')
    if args.small_cuts:
        if args.pairs != 6 or args.pole != [0, 2]:
            raise ValueError('small cuts require the six-pair split (0, 2)')
        for a, b in pairs[2:]:
            for side in (a, b):
                for i, j, k in combinations(absolute, 3):
                    f.clauses.append([-side[i], -side[j], -side[k]])
    for a, b in pairs:
        for p in POINTS:
            forbidden = [q for q in POINTS if not allowed[p][q]]
            f.clauses.extend([[-a[p], -b[q]] for q in forbidden])
            for left, right in [(a, b), (b, a)]:
                if p in frozen:
                    f.clauses.append([left[p] if f.signs[left[p]] else -left[p]])
                else:
                    # Enlarge legal rectangles on free points until maximal.
                    f.clauses.append([left[p]] + [right[q] for q in forbidden])
    for a in singles:
        f.clauses.append([a[pole]])
        for i in POINTS:
            if i in absolute:
                f.clauses.append([-a[i]])
                continue
            forbidden = [j for j in POINTS if j not in absolute and not allowed[i][j]]
            f.clauses.extend([[-a[i], -a[j]] for j in forbidden if j < i])
            f.clauses.append([a[i]] + [a[j] for j in forbidden])

    if args.ordered:
        def trace(a):
            if not pinned:
                return tuple(f.signs[a[i]] for i in frozen)
            return tuple(pinned.get(a[i]) for i in [pole] + absolute)
        signature = lambda a: [a[i] for i in absolute]
        for k, (a, b) in enumerate(pairs):
            if trace(a) == trace(b):
                f.lex(signature(a) + signature(b), signature(b) + signature(a))
            for c, d in pairs[k + 1:]:
                for u, w in [(c, d), (d, c)]:
                    if (trace(a), trace(b)) == (trace(u), trace(w)):
                        f.lex(signature(a) + signature(b), signature(u) + signature(w))
        free = [p for p in absolute if p not in frozen]
        blocks = {}
        for p in free:
            key = tuple(pinned[a[p]] for a in anchor) if anchor is not None else ()
            blocks.setdefault(key, []).append(p)
        for block in blocks.values():
            for i, j in zip(block, block[1:]):
                f.lex([a[i] for pair in pairs for a in pair], [a[j] for pair in pairs for a in pair])
        for a, b in zip(singles, singles[1:]):
            f.lex(a, b)

    skips = []
    for i in POINTS:
        for j in (POINTS if unpaired else range(i, 21)):
            if not allowed[i][j] or (args.boundary_only and i not in absolute and j not in absolute):
                continue
            options = [f.both(a[i], b[j]) for a, b in pairs]
            if i != j:
                options.extend(f.both(a[j], b[i]) for a, b in pairs)
            if i not in absolute and j not in absolute:
                options.extend(f.both(a[i], a[j]) for a in singles)
            options.extend(f.both(a[i], b[j]) for a, b in unpaired)
            if args.holes and (i == j or unpaired):
                skip = f.var(i == j and i == 6)
                options.append(skip)
                skips.append(skip)
            f.clauses.append(options)
    if unpaired and args.holes:
        # Prefix flags count omissions up to the allowed budget.
        flags = []
        for skip in skips:
            next_flags = [f.var() for _ in range(args.holes)]
            f.clauses.append([-skip, next_flags[0]])
            for k, flag in enumerate(flags):
                f.clauses.append([-flag, next_flags[k]])
                f.clauses.append([-flag, -skip] + next_flags[k + 1:k + 2])
            flags = next_flags
    else:
        for group in combinations(skips, args.holes + 1):
            f.clauses.append([-v for v in group])
    return f, pairs, singles, rows, unpaired


def check_model(args, f, pairs, singles, rows, unpaired):
    literals = [int(v) for line in args.model.read_text().splitlines() if line.startswith('v ')
                for v in line.split()[1:] if int(v)]
    assignment = {abs(x): x > 0 for x in literals}
    value = lambda v: assignment[v] != f.signs[v]
    mask = lambda bits: sum(value(v) << i for i, v in enumerate(bits))
    shapes = [(mask(a), mask(b)) for a, b in pairs]
    folded = shapes + [(b, a) for a, b in shapes] + [(mask(a), mask(a)) for a in singles]
    folded.extend((mask(a), mask(b)) for a, b in unpaired)
    boxes = [(a, sum((b >> j & 1) << c for j, c in enumerate(POLARITY))) for a, b in folded]
    assert len(boxes) == args.budget
    missing = []
    for i in POINTS:
        for j in POINTS:
            hit = any((a >> i & b >> j) & 1 for a, b in boxes)
            assert not (hit and rows[i] >> j & 1)
            if not hit and not (rows[i] >> j & 1):
                missing.append((i, j))
    absolute = [i for i in POINTS if rows[i] >> POLARITY[i] & 1]
    relevant = [(i, j) for i, j in missing if not args.boundary_only or i in absolute or POLARITY.index(j) in absolute]
    assert len(relevant) <= args.holes
    print(f'{len(boxes)} legal rectangles cover {336 - len(missing)} cells, with {len(relevant)} required cells missing.')
    if args.witness:
        args.witness.write_text(''.join(f'{a} {b}\n' for a, b in boxes))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cnf', type=Path)
    parser.add_argument('--budget', type=int, choices=(14, 15), default=14)
    parser.add_argument('--free', type=int, choices=range(32), default=31, help='five-bit mask of free boundary points')
    parser.add_argument('--pairs', type=int, choices=range(1, 8), default=6)
    parser.add_argument('--unmatched', type=int, choices=(0, 2), default=0,
                        help='number of additional rectangles free of the transpose constraint')
    parser.add_argument('--holes', type=int, choices=(0, 1, 2), default=1, help='permitted diagonal holes')
    parser.add_argument('--ordered', action='store_true', help='break label symmetries on the five absolute points')
    parser.add_argument('--pole', nargs=2, type=int, metavar=('BOTH', 'ONE'),
                        help='pairs containing the pole on both sides or on one side')
    parser.add_argument('--anchor', nargs=2, type=int, metavar=('LEFT', 'RIGHT'),
                        help='sizes of the first two-sided boundary cut, after relabeling')
    parser.add_argument('--small-cuts', action='store_true', help='bound each two-sided boundary cut by two points per side')
    parser.add_argument('--boundary-only', action='store_true', help='require coverage only on rows or columns of absolute points')
    parser.add_argument('--model', type=Path, help='independently score a CaDiCaL SAT model on all original cells')
    parser.add_argument('--witness', type=Path, help='with --model, save the row/column masks')
    args = parser.parse_args()
    result = make(args)
    result[0].save(args.cnf)
    if args.model:
        check_model(args, *result)
