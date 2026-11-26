"""Audit the geometry and regenerate or verify the 31 symmetric exclusions."""
import argparse
import csv
import hashlib
from itertools import combinations, permutations
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
from symmetric import board, POINTS

HERE = Path(__file__).resolve().parent
CHECKER = HERE / 'CheckCover.lean'


def audit_relabeling():
    _, allowed, _, _ = board()
    absolute = [i for i in POINTS if not allowed[i][i]]
    pole, = [i for i in POINTS if i not in absolute and not any(allowed[i][a] for a in absolute)]
    inside = set(POINTS) - set(absolute) - {pole}
    direction = {}
    for p in inside:
        direction[p], = [k for k, a in enumerate(absolute) if not allowed[p][a]]
    triangles = [t for t in combinations(sorted(inside), 3)
                 if all(not allowed[p][q] for p, q in combinations(t, 2))]
    assert len(triangles) == 10
    # A Petersen vertex is the pair of letters absent from a forbidden triangle.
    vertices = [frozenset(range(5)) - {direction[p] for p in t} for t in triangles]
    assert len(set(vertices)) == 10 and all(len(v) == 2 for v in vertices)
    label = {p: frozenset(v for v, t in zip(vertices, triangles) if p in t) for p in inside}
    assert len(set(label.values())) == 15
    assert all(len(edge) == 2 and len(set.union(*(set(x) for x in edge))) == 4 for edge in label.values())
    reverse = {e: p for p, e in label.items()}
    for pi in permutations(range(5)):
        points = {a: absolute[pi[k]] for k, a in enumerate(absolute)}
        points[pole] = pole
        for p, edge in label.items():
            image = frozenset(frozenset(pi[k] for k in v) for v in edge)
            points[p] = reverse[image]
        assert len(set(points.values())) == 21
        assert all(allowed[i][j] == allowed[points[i]][points[j]] for i in POINTS for j in POINTS)
    print('All 120 boundary permutations preserve all 441 entries.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('build_dir', type=Path)
    parser.add_argument('--lean-bin', type=Path, help='also generate LRAT and verify it with this Lean 4.36 bin directory')
    args = parser.parse_args()
    out = args.build_dir.resolve()
    out.mkdir(exist_ok=True, parents=True)
    audit_relabeling()
    lean = (HERE/'SymmetricPlane.lean').read_text()
    data = lean.split('def fifteen : List (Nat × Nat) :=')[1].split(']')[0]
    boxes = re.findall(r'\((\d+), (\d+)\)', data)
    assert len(boxes) == 15
    (out/'fifteen.txt').write_text(''.join(f'{a} {b}\n' for a, b in boxes))
    rows = list(csv.DictReader((HERE/'symmetric-replay.tsv').read_text().splitlines(), delimiter='\t'))
    assert len(rows) == len({r['case'] for r in rows}) == 31
    for r in rows:
        problem = out / (r['case'] + '.cnf')
        subprocess.run([sys.executable, str(HERE/'symmetric.py'), str(problem), *r['arguments'].split()], check=True)
        if hashlib.sha256(problem.read_bytes()).hexdigest() != r['cnf_sha256']:
            sys.exit('CNF differs from the checked formula for ' + r['case'])
        if args.lean_bin:
            tool = args.lean_bin.resolve()
            proof = problem.with_suffix('.lrat')
            if not proof.is_file():
                run = subprocess.run([tool/'cadical', '-q', '--lrat', '--phase=false', problem, proof], cwd=out,
                                     stdout=subprocess.DEVNULL)
                if run.returncode != 20:
                    sys.exit(f"{r['case']} solver exit {run.returncode}")
            verdict = subprocess.run([tool/'lean', '--run', CHECKER, problem, proof], cwd=out,
                                     text=True, capture_output=True, check=True)
            if f"Verified LRAT for {r['clauses']} clauses" not in verdict.stdout:
                sys.exit('Missing Lean LRAT verdict for ' + r['case'])
            print(r['case'], verdict.stdout.strip(), flush=True)
    print(f"{len(rows)} CNF hashes matched" + (' and all proofs passed.' if args.lean_bin else '.'))


if __name__ == '__main__':
    main()
