"""Recreate the Lean census shards from the kernel-checked literal host matrices."""
import argparse
import re
from functools import cache
from pathlib import Path

SOURCE = Path(__file__).resolve().parents[3] / "lean/PEqualNP/ThreeGateGain"
HOST_IDS = (4, 5, 8, 10, 12)
MAX_WORK = 2200
DECLARATIONS_PER_FILE = 80


def read_rows(host):
    source = (SOURCE / 'FiniteCatalogue.lean').read_text()
    table = re.search(r'def hostBits [^\n]+\n  #\[([\s\d,]+)\]\[i\.val\]!', source)
    if table is None:
        raise ValueError('Expected a 16-entry literal hostBits table')
    masks = [int(n) for n in table[1].split(',')]
    if len(masks) != 16:
        raise ValueError('Unexpected host count')
    return [masks[host] >> (27*i) & ((1 << 27)-1) for i in range(27)]


def lean_list(items):
    return '[' + ','.join(map(str, items)) + ']'


def generate(host):
    rows = read_rows(host)
    pool = tuple(i for i, row in enumerate(rows) if row)
    suffixes = {}
    declarations = []

    @cache
    def state(chosen):
        if not chosen:
            return 0, ()
        union, private = state(chosen[1:])
        row = rows[chosen[0]]
        return union | row, (row & ~union,) + tuple(domain & ~row for domain in private)

    def emit_state(chosen):
        union, private = state(chosen)
        return f'⟨{union},{lean_list(private)}⟩'

    def available(row_leaves):
        forbidden, _ = state(row_leaves)
        return tuple(i for i in pool if not (forbidden >> i) & 1)

    def valid(chosen):
        return all(state(chosen)[1])

    def extend(row_stage, row_leaves, col_leaves, vertex):
        if row_stage:
            return (vertex,) + row_leaves, col_leaves
        return row_leaves, (vertex,) + col_leaves

    @cache
    def weight(row_stage, row_leaves, col_leaves, remaining):
        # This estimate chooses locations to split the proof. Lean checks each
        # emitted branch, so timings and weights have no mathematical role.
        if not remaining:
            if row_stage:
                return weight(False, row_leaves, (), available(row_leaves))
            t = len(row_leaves) + len(col_leaves)
            r = state(row_leaves)[0].bit_count()
            c = state(col_leaves)[0].bit_count()
            return 100 if 17*t + 3*(2*len(pool)-r-c) > 158 else 7
        tail = remaining[1:]
        skipped = weight(row_stage, row_leaves, col_leaves, tail) + 1
        r, c = extend(row_stage, row_leaves, col_leaves, remaining[0])
        return skipped + (weight(row_stage, r, c, tail) + 1 if valid(r if row_stage else c) else 0)

    def declare(target, proof):
        name = f'n{len(declarations)}'
        declarations.append(f'theorem {name} : {target} := {proof}\n')
        return name

    def visit(row_stage, row_leaves, col_leaves, remaining):
        chosen = row_leaves if row_stage else col_leaves
        bank_name = suffixes.setdefault(remaining, f'b{len(suffixes)}')
        if row_stage:
            test = f'(leafCols {host} bank)'
        else:
            test = f'(leafFrame {host} {lean_list(row_leaves)} {emit_state(row_leaves)})'
        target = f'fastVisit {test} {lean_list(chosen)} {emit_state(chosen)} {bank_name} = true'
        if weight(row_stage, row_leaves, col_leaves, remaining) <= MAX_WORK or (not remaining and not row_stage):
            return declare(target, 'by decide +kernel')
        if not remaining:
            columns = available(row_leaves)
            child = visit(False, row_leaves, (), columns)
            # Give the kernel the filtered bank equality explicitly. Matching
            # entire Boolean searches by conversion can replay the child.
            proof = (f'enterColumns {host} bank {lean_list(row_leaves)} {emit_state(row_leaves)} '
                     f'{bank_name} {suffixes[columns]} (by decide +kernel) (by decide +kernel) {child}')
            return declare(target, proof)
        tail = remaining[1:]
        skipped = visit(row_stage, row_leaves, col_leaves, tail)
        r, c = extend(row_stage, row_leaves, col_leaves, remaining[0])
        if valid(r if row_stage else c):
            included = visit(row_stage, r, c, tail)
            return declare(target, f'join_live {skipped} {included}')
        return declare(target, f'join_dead {skipped} (by decide +kernel)')

    def row_pairs(vertices):
        return lean_list(f'({i},{rows[i]})' for i in vertices)

    theorem = visit(True, (), (), pool)
    preamble = (f'namespace GainFinite.F{host}\nopen GainFinite\nset_option maxHeartbeats 0\n'
                'set_option maxRecDepth 200000\n\n')
    closing = f'\nend GainFinite.F{host}\n'
    previous = f'FiniteB{host:02}'
    banks = f'def bank : List (WordType × Nat) := {row_pairs(pool)}\n'
    for vertices, name in suffixes.items():
        banks += f'def {name} : List (WordType × Nat) := {row_pairs(vertices)}\n'
    yield previous + '.lean', 'import PEqualNP.ThreeGateGain.FiniteBranch\n\n' + preamble + banks + closing
    for start in range(0, len(declarations), DECLARATIONS_PER_FILE):
        name = f'FiniteV{host:02}P{start//DECLARATIONS_PER_FILE:03}'
        text = f'import PEqualNP.ThreeGateGain.{previous}\n\n' + preamble + '\n'.join(declarations[start:start+DECLARATIONS_PER_FILE])
        if start + DECLARATIONS_PER_FILE >= len(declarations):
            text += (f'\ntheorem passed : quickHost {host} = true := by\n  rw [← leafHost_sparse]\n'
                     f'  have pool_correct : sparseRows {host} = bank := by decide +kernel\n'
                     f'  rw [pool_correct]\n  exact {theorem}\n')
        yield name + '.lean', text + closing
        previous = name


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write to this existing directory. Default checks existing files.')
    args = parser.parse_args()
    checked = 0
    for host in HOST_IDS:
        for filename, expected in generate(host):
            if args.output is not None:
                (args.output / filename).write_text(expected)
            elif (SOURCE / filename).read_text() != expected:
                raise SystemExit(f'{filename} differs from the generated proof')
            checked += 1
    print(f'{checked} Lean source files {"generated" if args.output is not None else "matched"}.')
