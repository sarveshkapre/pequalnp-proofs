"""Check each singleton profile, then derive the universal line-precursor instances."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import cache
from itertools import permutations
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "profiles"))
from profiles import SHAPES, permute
from mixing_bound_seven import find_reconstruction


def node(tokens):
    op = next(tokens)
    if op in ('p', 'l', 's'):
        return op
    assert op in ('&','|')
    return op, node(tokens), node(tokens)


def independent_codes(lower, upper, width, shape):
    """Scalar replay of the representative tree, including internal wire reuse."""
    pts = lines = 0
    def label(tree):
        nonlocal pts, lines
        if tree == 's':
            return 's'
        if tree == 'p':
            pts += 1
            return 'p', pts - 1
        if tree == 'l':
            lines += 1
            return 'l', lines - 1
        return tree[0], label(tree[1]), label(tree[2])
    down = label(node(iter(lower)))
    up = label(node(iter(upper)))
    assert (pts, lines) == (3,width)
    def eval_tree(tree, p, code, s):
        if tree == 's':
            return s
        if tree[0] == 'p':
            return p == tree[1] + 1
        if tree[0] == 'l':
            return bool(code & (1 << tree[1]))
        a = eval_tree(tree[1], p, code, s)
        b = eval_tree(tree[2], p, code, s)
        return a and b if tree[0] == '&' else a or b
    bits = [0]*8
    for code in range(1<<width):
        vals = [eval_tree(up,p,code,eval_tree(down,p,code,False)) for p in range(4)]
        if code==0:
            assert not any(vals)
        membership=sum(int(v)<<i for i,v in enumerate(vals[1:]))
        if not vals[0] and membership in SHAPES[shape]:
            bits[membership] |= 1<<code
    return tuple(bits)


@cache
def relabel_codes(bits, order):
    return sum(1<<permute(c, order) for c in range(1 << len(order)) if bits>>c & 1)


def normalize(bits, width, shape):
    kinds=SHAPES[shape]
    orders=[tuple(permute(k,r) for k in kinds) for r in permutations(range(3))]
    best=None
    for line_order in permutations(range(width)):
        moved = {k: relabel_codes(bits[k], line_order) for k in kinds}
        key=min(tuple(moved[k] for k in ordered) for ordered in orders)
        if best is None or key<best:
            best=key
    return best


def classify(raw, width, mixed):
    groups=defaultdict(Counter)
    counts=Counter()
    for row in raw.read_text().splitlines():
        shape, n, lower, upper, *entries=row.split('\t')
        bits=tuple(map(int, entries))
        assert independent_codes(lower, upper, width, shape) == bits
        groups[shape][normalize(bits,width,shape)] += int(n)
        counts[shape] += int(n)
    pending=[]
    for shape in sorted(groups):
        rest=Counter()
        for key, frequency in sorted(groups[shape].items()):
            by_kind=dict(zip(SHAPES[shape],key,strict=True))
            domain=1
            goals=[0]*3
            for kind, allowed in by_kind.items():
                assert domain & allowed == 0
                domain |= allowed
                for i in range(3):
                    if kind>>i & 1:
                        goals[i] |= allowed
            budget=13-mixed
            if find_reconstruction(width,domain,tuple(goals),8-budget) is not None:
                continue
            rest['classes']+=1
            rest['expressions']+=frequency
            pending.append(dict(shape=shape,total=13,line_gates=budget,boundary=width,
                         codes=[[i for i in range(1 << width) if v>>i & 1] for v in key],
                         expressions=frequency))
        print(shape,'feasible',counts[shape],'canonical classes',len(groups[shape]),'pending',dict(rest))
    return pending


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('raw',type=Path)
    p.add_argument('output',type=Path)
    p.add_argument('--width',type=int,default=5)
    a=p.parse_args()
    cases=classify(a.raw,a.width,3+a.width)
    a.output.write_text(json.dumps(cases,indent=1)+'\n')
