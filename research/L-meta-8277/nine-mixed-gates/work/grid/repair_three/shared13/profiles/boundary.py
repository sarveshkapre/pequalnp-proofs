"""Bound line signals entering the mixed gates, even with arbitrary monotone decoding."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from itertools import product
import json
from pathlib import Path
from line_prefix import check_model, encode
from line_order import lex_ge
from run_first_mix import solve_and_replay
from split import project
from sweep import digest


def separations(targets):
    width = max(row.bit_length() for row in targets)
    return [(i, j) for i, j in product(range(width), repeat=2)
            if any((r >> i & 1) and not (r >> j & 1) for r in targets)]


def boundary_rules(enc, signals, targets):
    for before, after in zip(signals, signals[1:]):
        lex_ge(enc, before, after)
    for code in zip(*signals):
        enc.clause(*code)
    for pos, neg in separations(targets):
        witnesses = []
        for signal in signals:
            w = enc.var()
            enc.clause(-w, signal[pos])
            enc.clause(-w, -signal[neg])
            witnesses.append(w)
        enc.clause(*witnesses)


def run(case, root, seconds):
    shape, width, gates = case
    path = root / f"{shape}-{width}-{gates}"
    path.mkdir()
    spec = dict(shape=shape, boundary=width, line_gates=gates)
    cnf = path / 'input.cnf'
    encoded = encode(cnf, spec, boundary_rules)
    verdict, _, proof, actions = solve_and_replay(path, seconds)
    row = dict(**spec, verdict=verdict, sha256=digest(cnf), lrat=proof, actions=actions)
    if verdict == 'PROJECTED_SAT':
        masks = check_model(spec, encoded, (path / 'solver.txt').read_text())
        _, targets, lines = project(tuple(map(int,shape)), 'universal')
        assert all(any((m >> i & 1) and not (m >> j & 1) for m in masks)
                   for i, j in separations(targets))
        assert all(any(m >> i & 1 for m in masks) for i in range(len(lines)))
        row['masks'] = masks
    print(shape, width, gates, verdict, flush=True)
    return row


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('cache', type=Path)
    p.add_argument('ledger', type=Path)
    p.add_argument('--gates', type=int, nargs='+', required=True)
    p.add_argument('--width', type=int, nargs='+', required=True)
    p.add_argument('--seconds', type=int, default=12)
    a = p.parse_args()
    if a.cache.exists() or a.ledger.exists():
        p.error('choose a fresh cache and ledger')
    a.cache.mkdir(parents=True)
    with ThreadPoolExecutor(max_workers=4) as pool:
        rows = list(pool.map(lambda spec: run(spec, a.cache, a.seconds),
                             product(('012','013'), a.width, a.gates)))
    a.ledger.write_text(json.dumps(rows,indent=2) + '\n')
