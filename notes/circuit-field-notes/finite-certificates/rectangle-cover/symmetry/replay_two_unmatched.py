"""Regenerate the complete two-unmatched census and optionally replay its LRAT proofs."""
import argparse
import csv
from hashlib import sha256
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
from replay_symmetric import audit_relabeling, CHECKER
from two_unmatched import encode, check_model

HERE = Path(__file__).resolve().parent
# These broad cases needed smaller certificates. Every legal anchor size is
# generated below. A single branch uses the small-cut argument in the note.
SPLIT = {(5, (0, 0, 2)), (5, (0, 1, 0)), (5, (0, 1, 1)), (5, (0, 2, 0)), (6, (0, 2, 2))}


def cases():
    for k in (2, 3, 4):
        yield f'all-{k}', (k,)
    for k in (5, 6):
        for both in range(k + 1):
            for one in range(k - both + 1):
                cuts = k - both - one
                for special in range(3):
                    pole = (both, one, special)
                    if cuts + (special == 0) < 3:
                        continue
                    label = f'{k}-{both}{one}{special}'
                    if (k, pole) not in SPLIT:
                        yield 'core-' + label, (k, pole)
                        continue
                    for a in range(1, 5):
                        for b in range(1, min(a, 5 - a) + 1):
                            if cuts * a * b + 6 * (special == 0) < 10:
                                continue
                            small = (k, pole, a, b) == (5, (0, 1, 1), 2, 2)
                            prefix = 'small-' if small else 'an-'
                            yield f'{prefix}{label}-{a}{b}', (k, pole, (a, b), small)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('scratch', type=Path)
    parser.add_argument('--lean-bin', type=Path, help='also generate and check the proof for each CNF')
    args = parser.parse_args()
    out = args.scratch.resolve()
    out.mkdir(parents=True, exist_ok=True)
    audit_relabeling()
    with (HERE / 'two-unmatched-replay.tsv').open() as stream:
        manifest = list(csv.DictReader(stream, delimiter='\t'))
    records = {r['case']: r for r in manifest}
    checklist = list(cases())
    assert len(checklist) == len(records) == len(manifest)
    assert set(records) == {name for name, _ in checklist}
    for name, params in checklist:
        cnf = out / (name + '.cnf')
        encode(*params)[0].save(cnf)
        assert sha256(cnf.read_bytes()).hexdigest() == records[name]['cnf_sha256'], name
        if args.lean_bin:
            tool = args.lean_bin.resolve()
            proof = cnf.with_suffix('.lrat')
            if not proof.exists():
                result = subprocess.run([tool/'cadical', '-q', '--phase=false', '--lrat', cnf, proof],
                                        stdout=subprocess.DEVNULL, cwd=out)
                assert result.returncode == 20, name
            verdict = subprocess.run([tool/'lean', '--run', CHECKER, cnf, proof], cwd=out,
                                     capture_output=True, text=True, check=True)
            assert f"Verified LRAT for {records[name]['clauses']} clauses" in verdict.stdout, name
            print(name, verdict.stdout.strip(), flush=True)
    if args.lean_bin:
        control = encode(5, control=True)
        cnf = out / 'positive.cnf'
        control[0].save(cnf)
        model = out / 'positive.model'
        with model.open('w') as sink:
            result = subprocess.run([args.lean_bin.resolve()/'cadical', '-q', cnf], cwd=out, stdout=sink)
        assert result.returncode == 10
        check_model(model, control, True)
    print(f'{len(checklist)} formula hashes matched.')


if __name__ == '__main__':
    main()
