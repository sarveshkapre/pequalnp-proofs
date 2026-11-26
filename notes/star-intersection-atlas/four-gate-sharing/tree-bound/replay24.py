"""Classify the 24-vertex induced trees and verify the formula for each shape."""
from pathlib import Path
import gzip
import json
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREVIOUS = runpy.run_path(str(HERE.parent / 'five-leaves' / 'extremal.py'))
STAR = PREVIOUS['STAR']


def matching_seeds(rows):
    """Choose diagonal pairs; in each extension keep a forest after contraction."""
    incoming_rows = [sum(1 << i for i, row in enumerate(rows) if row >> j & 1)
                     for j in range(len(rows))]
    def grow(chosen, candidates, parts, contacts):
        size = chosen.bit_count()
        if (size == 10 and contacts <= 5) or (size == 11 and contacts <= 8):
            yield chosen, size, contacts
        if size == 11 or size + candidates.bit_count() < 10 or contacts > 8:
            return
        while candidates and size + candidates.bit_count() >= 10:
            vertex = candidates & -candidates
            candidates ^= vertex
            j = vertex.bit_length() - 1
            outgoing = rows[j] & chosen
            incoming = incoming_rows[j] & chosen
            if outgoing & incoming:
                continue
            hits = outgoing | incoming
            if any((part & hits).bit_count() > 1 for part in parts):
                continue
            merged = vertex | sum(part for part in parts if part & hits)
            components = [part for part in parts if not part & hits] + [merged]
            remaining = candidates & ~(rows[j] & incoming_rows[j])
            yield from grow(chosen | vertex, remaining, components, contacts + hits.bit_count())
    return grow(0, (1 << len(rows)) - 1, [], 0)


def main(program):
    lines = []
    for shape, count in zip(STAR['HOSTS'], (41, 0, 17, 213, 68), strict=True):
        table, pairs = STAR['maximal_pairs'](shape)
        pairs = [(a,b) for a,b in pairs if table[a] and table[b]]
        rows, cols = zip(*pairs)
        seeds = list(matching_seeds(PREVIOUS['incidence'](table, rows, cols)))
        assert len(seeds) == count
        print(f'{count} matching seeds recovered.', flush=True)
        lines.extend([''.join(str(int(x)) for x in table), str(count)])
        for mask, size, contacts in seeds:
            words = [w for i, pair in enumerate(pairs) if mask >> i & 1 for w in pair]
            lines.append(' '.join(map(str, (size, contacts, *words))))
    result = subprocess.run([str(Path(program).resolve())], input='\n'.join(lines)+'\n',
                            capture_output=True, text=True, check=True)
    print(result.stderr, end='')
    by_host = [set() for _ in range(5)]
    for line in result.stdout.splitlines():
        host, tree = line.split()
        by_host[int(host)].add(tree)
    assert [len(x) for x in by_host] == [582, 0, 1316, 2855, 2309]
    trees = set.union(*by_host)
    with gzip.open(HERE / 'order24.json.gz', 'rt') as f:
        cert = json.load(f)
    assert trees == cert.keys() and len(trees) == 3155
    for tree, words in cert.items():
        rows, n = PREVIOUS['decode'](tree)
        assert len(rows) + n == 24 and PREVIOUS['tree_code'](rows,n) == tree
        assert len(words) == len(rows) and all(0 <= w < 64 for w in words)
        for j in range(n):
            shared = 0
            for i, row in enumerate(rows):
                if row >> j & 1:
                    shared |= words[i]
            assert all(bool(row >> j & 1) == (words[i] & ~shared == 0)
                       for i, row in enumerate(rows))
    print('All 3,155 order-24 certificates passed every cell.')


if __name__ == '__main__':
    if not __debug__ or len(sys.argv) != 2:
        raise SystemExit('Run with assertions enabled and supply the compiled order24 checker.')
    main(sys.argv[1])
