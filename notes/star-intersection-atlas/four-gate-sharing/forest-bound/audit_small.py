"""Forward check using all reduced supertrees, including every positive one."""
import gzip
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
FOREST = runpy.run_path(str(HERE/'components.py'))
TREE = FOREST['TREE']
BASE = FOREST['BASE']


def centroid_code(code):
    adj,sides,parts = FOREST['decode'](code)

    def descend(v,p):
        return '('+''.join(sorted(descend(w,v) for w in adj[v] if w != p))+')'

    def size(v,p):
        return 1+sum(size(w,v) for w in adj[v] if w != p)

    oriented = [[],[]]
    for part in parts:
        centers = [v for v in part if all(2*size(w,v)<=len(part) for w in adj[v])]
        assert len(centers) in (1,2)
        for flip in (0,1):
            oriented[flip].append(min(str(flip ^ sides[v])+descend(v,-1) for v in centers))
    return min(''.join(sorted(words)) for words in oriented)


def supertrees(order):
    if order == 23:
        with gzip.open(BASE/'order23.bin.gz','rb') as f:
            for tree in TREE['assemble'](23,11):
                tag, = f.read(1)
                size = tag or len(TREE['matrix'](tree)[0])
                assert len(f.read(size)) == size
                yield tree, tag == 0
            assert not f.read(1)
    else:
        cert = json.loads((BASE/'small.json').read_text())
        exceptional = {k for k,(tag,*_) in cert.items() if tag=='m' and len(k)==2*order}
        # Even orders may emit the same unrooted tree from both centroids.
        # Repeating that deletion leaves the same existence flag.
        for tree in TREE['assemble'](order,order//2):
            yield tree, TREE['canonical'](TREE['adjacency'](tree)) not in exceptional


def main(program):
    special = json.loads((HERE/'small.json').read_text())
    for order in (21,22,23):
        with tempfile.TemporaryFile(mode='w+') as cases:
            for tree, positive in supertrees(order):
                print(int(positive),tree,file=cases)
            cases.seek(0)
            result = subprocess.run([program],stdin=cases,capture_output=True,text=True,check=True)
        expected = {centroid_code(key) for key in special if key.count('(')==order-1}
        assert set(result.stdout.splitlines()) == expected
        print(f'Order {order-1}: {result.stderr.strip()}',flush=True)


if __name__ == '__main__':
    if not __debug__ or len(sys.argv)!=2:
        raise SystemExit('Enable assertions and pass the compiled audit_small executable.')
    main(str(Path(sys.argv[1]).resolve()))
