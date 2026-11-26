"""Regenerate the eight-mixed-gate residual formulas and check their LRAT proofs."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parent
EIGHT = ROOT / 'work/grid/repair_three/shared13/eight'
sys.path.insert(0, str(EIGHT / 'prefix'))
from solve import encode, prepare
sys.path.insert(0, str(EIGHT))
from check_certificates import verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', type=Path, help='also write cases in the directory layout used by the Lean replay scripts (new directory)')
    cache = parser.parse_args().cache
    if not __debug__:
        parser.error('run with assertions enabled')
    if cache is not None:
        cache.mkdir(parents=True, exist_ok=False)
    totals = {'tree': {'012': 153, '013': 14}, 'fan-verify': {'012': 20, '013': 9}}
    inputs = {'tree': [EIGHT / 'tree/three.json', EIGHT / 'tree/four.json'],
              'fan-verify': [EIGHT / 'fan/prefixes.json']}
    checked = set()
    archive_files = set()
    with ZipFile(ROOT / 'certificates.zip') as archive, TemporaryDirectory() as temp:
        cnf = Path(temp) / 'case.cnf'
        for label, expected in totals.items():
            classes = json.loads((EIGHT / 'prefix' / f'{label}-classes.json').read_text())
            records = json.loads((EIGHT / 'prefix' / f'{label}-results.json').read_text())
            assert classes == prepare(inputs[label])
            assert Counter(c['shape'] for c in classes) == expected
            for i, (case, record) in enumerate(zip(classes, records, strict=True)):
                assert record['index'] == i and record['verdict'] == 'VERIFIED_UNSAT'
                assert all(case[k] == record[k] for k in ('shape', 'boundary', 'line_gates'))
                encode(cnf, case)
                formula_name = record['sha256'] + '.cnf'
                proof_name = record['lrat'] + '.lrat'
                archive_files.update((formula_name, proof_name))
                formula = archive.read(formula_name)
                proof = archive.read(proof_name)
                assert formula == cnf.read_bytes() and sha256(formula).hexdigest() == record['sha256']
                assert sha256(proof).hexdigest() == record['lrat']
                pair = (formula_name, proof_name)
                if pair not in checked:
                    verify(formula, proof)
                    checked.add(pair)
                if cache is not None:
                    folder = cache / f'L-meta-8277-eight-{label}' / f'{i:04d}'
                    folder.mkdir(parents=True)
                    (folder / 'input.cnf').write_bytes(formula)
                    (folder / 'proof.lrat').write_bytes(proof)
            print(f'{label}: {len(classes)} classes rebuilt and checked.')
        assert len(checked) == 175 and len({f for f, p in checked}) == 175
        assert sorted(archive_files) == sorted(archive.namelist())
    print('196 entries, 175 distinct formulas. Each derived the empty clause.')


if __name__ == '__main__':
    main()
