"""Replay the disconnected-forest theorem with Python 3.10+ and the boundary checker."""
from pathlib import Path
from itertools import combinations
import argparse
import gzip
import json
import runpy
import subprocess

HERE = Path(__file__).resolve().parent
F = runpy.run_path(str(HERE / 'components.py'))
T = F['TREE']
BASE = F['BASE']
BOUNDARY = runpy.run_path(str(BASE / 'replay24.py'))
TREE_PROOF = runpy.run_path(str(BASE / 'replay.py'))
CASES = {
    (23, 2): (441, 0, 695, 1552, 1295),
    (23, 3): (31, 0, 42, 81, 79),
    (24, 2): (63, 0, 122, 221, 217),
}


def controls():
    # Two copies of P5 have inequivalent relative orientations.
    code = '0((())(()))0((())(()))'
    adj, sides, parts = F['decode'](code)
    key = F['key'](adj, sides)
    assert key == F['key'](adj, [s ^ 1 for s in sides])
    for i in parts[0]:
        sides[i] ^= 1
    assert key != F['key'](adj, sides)
    # Universal-row trees, with a bare column and isolates on both shores.
    options = [sum(1 << x for x in pair) for pair in combinations(range(5), 2)]
    for arms in range(11):
        labels = options[:arms]
        rows = [32, *labels, 63]
        cols = [31 ^ w for w in labels] + [31, 63]
        for i, x in enumerate(rows):
            for j, y in enumerate(cols):
                edge = (i == 0 and j <= arms) or (1 <= i <= arms and i-1 == j)
                assert (x & y == 0) == edge


def verify_small():
    exceptional = {21: set(), 22: set(), 23: set()}
    with gzip.open(BASE / 'order23.bin.gz', 'rb') as f:
        for tree in T['assemble'](23, 11):
            rows, _ = T['matrix'](tree)
            tag, = f.read(1)
            size = tag or len(rows)
            assert len(f.read(size)) == size
            if tag:
                exceptional[23].add(T['canonical'](T['adjacency'](tree)))
        assert not f.read(1)
    for tree, (kind, *_) in json.loads((BASE / 'small.json').read_text()).items():
        if kind == 'm':
            exceptional[len(tree)//2].add(tree)
    special = json.loads((HERE / 'small.json').read_text())
    used = set()
    for order, expected in [(21,(9,31,0)), (22,(137,444,0)), (23,(2591,8135,2))]:
        outside = exceptional[order]
        cases = {forest for tree in outside for forest in F['punctures'](tree)}
        hard = {k for k in cases if F['extension'](k, outside) is None}
        assert (len(outside), len(cases), len(hard)) == expected
        for code in hard:
            rows, n = F['matrix'](code)
            words = special[code]
            assert len(words) == len(rows)+n and all(type(x) == int and 0 <= x < 128 for x in words)
            for i, row in enumerate(rows):
                for j, y in enumerate(words[len(rows):]):
                    common = words[i] & y
                    assert bool(row >> j & 1) == (common & 31 == 0 or common & 96 == 0)
            used.add(code)
        print(f'Order {order-1}: {len(cases)} restrictions of exceptional trees, '
              f'{len(hard)} requiring an explicit formula.', flush=True)
    assert used == special.keys()


def host_witness(shape, order, parts, wiring, values):
    m, *labels = values
    assert len(labels) == order and 0 < m < order and all(0 <= w < 256 for w in labels)
    xs, ys = labels[:m], labels[m:]
    zero = BOUNDARY['STAR']['zero_cell']
    adj = [[] for _ in labels]
    for i, x in enumerate(xs):
        for j, y in enumerate(ys, m):
            if not zero(wiring, x & y):
                adj[i].append(j)
                adj[j].append(i)
    assert all(adj) and sum(map(len,adj)) == 2*(order-parts)
    assert sum(1 for _ in F['pieces'](adj, range(order))) == parts
    assert F['reduced'](adj) and F['key'](adj, [0]*m + [1]*len(ys)) == shape


def census(executable, inputs, order, parts, audit):
    args = [executable, str(order), str(parts)]
    if audit:
        args.append('--audit')
    run = subprocess.run(args, input=inputs, text=True, capture_output=True, check=True)
    sets = [set() for _ in range(5)]
    for line in run.stdout.splitlines():
        h, code, *raw = line.split()
        host = int(h)
        assert 0 <= host < 5 and code not in sets[host]
        sets[host].add(code)
        if audit:
            host_witness(code, order, parts, BOUNDARY['STAR']['HOSTS'][host], list(map(int, raw)))
        else:
            assert not raw
    assert tuple(map(len,sets)) == CASES[order, parts]
    return sets, run.stderr


def verify_large(executable, audit):
    inputs = BOUNDARY['census_input']()
    with gzip.open(HERE / 'formulas.json.gz', 'rt') as f:
        formulas = json.load(f)
    checked = set()
    for (order, parts), expected in CASES.items():
        sets, stats = census(executable, inputs, order, parts, False)
        if audit:
            other, independent_stats = census(executable, inputs, order, parts, True)
            assert other == sets and independent_stats == stats
        keys = set.union(*sets)
        assert len(keys) == {(23,2):1644, (23,3):83, (24,2):237}[order, parts]
        for k in keys:
            adj, sides, comps = F['decode'](k)
            assert len(adj) == order and len(comps) == parts and F['reduced'](adj)
            assert F['key'](adj,sides) == k and k not in checked
            rows, n = F['matrix'](k)
            words = formulas[k]
            assert all(type(w) == int and 0 <= w < 64 for w in words)
            TREE_PROOF['flat'](rows,n,words)
            checked.add(k)
        print(f'{order} vertices, {parts} components: {len(keys)} formulas; '
              f'host sizes {list(expected)}.', flush=True)
    assert checked == formulas.keys() and len(checked) == 1964
    if audit:
        print('Both exposed-vertex enumerations agree per host, including raw completion counts. '
              'Every reported host witness passed a fresh cell-by-cell reconstruction.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('boundary_checker', type=Path)
    parser.add_argument('--audit', action='store_true', help='also enumerate by total edges and components')
    args = parser.parse_args()
    controls()
    verify_small()
    verify_large(str(args.boundary_checker.resolve()), args.audit)
