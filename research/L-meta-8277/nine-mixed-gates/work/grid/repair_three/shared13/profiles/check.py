"""Verify saved exclusions, and exercise the same encoder with a passing line circuit per class."""
import argparse
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from itertools import permutations, product
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from line_prefix import SHAPES, check_model, encode, project
from profiles import HERE
from run_first_mix import TOOLS
from sweep import digest
from boundary import boundary_rules, separations


def make_control(case):
    free, rows, lines = project(tuple(map(int, case["shape"])), "universal")
    rules = dict(zip(SHAPES[case["shape"]], case["codes"], strict=True))
    classes = defaultdict(list)
    for j in range(len(lines)):
        classes[sum(((r >> j) & 1) << i for i, r in enumerate(rows))].append(j)
    masks = [sum(1 << j for kind, members in classes.items() if rules[kind][0] >> i & 1 for j in members)
             for i in range(case["boundary"])]
    # Select one permissible code per line, and build each requested OR from singletons.
    # Pairs of primary wires are ready first. Each newly appended wire can only be read later.
    gates = []
    outputs = []
    for mask in masks:
        if mask in free:
            outputs.append(("raw", mask))
            continue
        leaves = [("raw", 1 << j) for j in range(len(lines)) if mask >> j & 1]
        value = leaves[0]
        for leaf in leaves[1:]:
            gates.append((value, leaf))
            value = "gate", len(gates) - 1
        outputs.append(value)

    def priority(w):
        return -1 if w[0] == "raw" else w[1]

    ordered = []
    built = {}
    def rename(w):
        return w if w[0] == "raw" else ("gate", built[w[1]])
    while len(built) < len(gates):
        ready = [i for i, pins in enumerate(gates) if i not in built and
                 all(w[0] == "raw" or w[1] in built for w in pins)]
        i = min(ready, key=lambda i: max(priority(rename(w)) for w in gates[i]))
        pair = sorted((rename(w) for w in gates[i]), key=priority)
        built[i] = len(ordered)
        ordered.append(pair)
    outputs = [rename(w) for w in outputs]

    # Normalize actual singleton names within each row-membership class.
    # Select the lexicographically largest raw-operand matrix, allowing pin swaps.
    def bits(m):
        return tuple((m >> j) & 1 for j in range(len(lines)))
    best = None
    for groups in product(*(permutations(group) for group in classes.values())):
        mapping = dict(zip((i for group in classes.values() for i in group),
                           (j for group in groups for j in group), strict=True))
        def move(w):
            return w if w[0] == "gate" else ("raw", sum(1 << mapping[i] for i in mapping if w[1] >> i & 1))
        pairs = []
        for a, b in ordered:
            a, b = move(a), move(b)
            if a[0] == b[0] == "raw" and bits(a[1]) < bits(b[1]):
                a, b = b, a
            pairs.append((a, b))
        matrix = tuple(bits(w[1] if w[0] == "raw" else 0) for pins in pairs for w in pins)
        if best is None or matrix > best:
            best = matrix
            plant = pairs, [move(w) for w in outputs]
    return plant


def check_one(case, record, idx, cache):
    with TemporaryDirectory() as temp:
        folder = Path(temp)
        path = folder / 'case.cnf'
        encode(path, case)
        assert digest(path) == record["sha256"] and record["verdict"] == "VERIFIED_UNSAT"
        original = cache / str(idx)
        proof = original / 'proof.lrat'
        assert digest(proof) == record["lrat"]
        result = subprocess.run([TOOLS / "lean", "--run", HERE.parents[2] / 'bounds/CheckCover.lean',
                                 path, proof], check=True, capture_output=True, text=True)
        assert f"and {record['actions']} actions." in result.stdout

        gates, outputs = make_control(case)
        control = dict(case, line_gates=len(gates))
        encoded = encode(path, control)
        specs, taps, _, _ = encoded
        units = []
        def pin(side, w):
            selectors, bits = side
            units.append(selectors[0] if w[0] == "raw" else selectors[w[1] + 1])
            if w[0] == "raw":
                units.extend(v if w[1] >> j & 1 else -v for j, v in enumerate(bits))
        for (left, right, op), (a, b) in zip(specs, gates, strict=True):
            pin(left, a)
            pin(right, b)
            units.append(-op)
        for tap, out in zip(taps, outputs, strict=True):
            pin(tap, out)
        hdr, body = path.read_text().split('\n', 1)
        _, _, width, clauses = hdr.split()
        path.write_text(f"p cnf {width} {int(clauses)+len(units)}\n" + body +
                        "".join(f"{u} 0\n" for u in units))
        solved = subprocess.run([TOOLS / "cadical", "-q", path], capture_output=True, text=True)
        assert solved.returncode == 10, (case, solved.stdout[-500:])
        check_model(control, encoded, solved.stdout)


def verify_boundaries(root):
    minima = {0: 7, 1: 7, 2: 6, 3: 5, 4: 5, 5: 5}
    verdicts = {}
    for file, suffix in [('boundary', 'line-boundary'), ('boundary-mid', 'boundary-mid'),
                         ('boundary-raw', 'boundary-raw')]:
        for row in json.loads((HERE / f'{file}.json').read_text()):
            s, w, n = row['shape'], row['boundary'], row['line_gates']
            case = root / f'L-meta-8277-shared13-{suffix}' / f'{s}-{w}-{n}'
            with TemporaryDirectory() as temp:
                cnf = Path(temp) / 'case.cnf'
                encoded = encode(cnf, row, boundary_rules)
                assert digest(cnf) == row['sha256']
                if row['verdict'] == 'VERIFIED_UNSAT':
                    proof = case / 'proof.lrat'
                    assert digest(proof) == row['lrat']
                    result = subprocess.run([TOOLS / 'lean', '--run', HERE.parents[2] / 'bounds/CheckCover.lean',
                                             cnf, proof], capture_output=True, text=True, check=True)
                    assert f"and {row['actions']} actions." in result.stdout
                else:
                    assert row['verdict'] == 'PROJECTED_SAT'
                    masks = check_model(row, encoded, (case / 'solver.txt').read_text())
                    assert masks == row['masks']
                    _, targets, _ = project(tuple(map(int, s)), 'universal')
                    assert all(any((m >> a & 1) and not (m >> b & 1) for m in masks)
                               for a, b in separations(targets))
                verdicts[s, w, n] = row['verdict']
    for s in SHAPES:
        for n, w in minima.items():
            assert verdicts[s, w, n] == 'PROJECTED_SAT'
            # UNSAT for a wider interface or a larger preparation budget also suffices.
            assert any(v == 'VERIFIED_UNSAT' and s0 == s and k >= w-1 and g >= n
                       for (s0,k,g),v in verdicts.items())
    print('Line-signal minima for 0 to 5 preparation gates verified in both shapes:', list(minima.values()))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cache_root', type=Path)
    args = parser.parse_args()
    for name, count, k in [('six',3,6), ('seven',28,7)]:
        cases = json.loads((HERE / f'{name}.json').read_text())['remaining']
        results = json.loads((HERE / f'{name}-prefix.json').read_text())
        assert len(cases) == len(results) == count
        folder = args.cache_root / f'L-meta-8277-shared13-prefix{k}'
        with ThreadPoolExecutor(max_workers=4) as pool:
            list(pool.map(lambda x: check_one(x[1], x[2], x[0], folder),
                          ((i,case,result) for i,(case,result) in enumerate(zip(cases,results,strict=True)))))
        print(name, count, 'regenerated CNFs, LRAT replays, and decoded SAT controls')
    verify_boundaries(args.cache_root)
