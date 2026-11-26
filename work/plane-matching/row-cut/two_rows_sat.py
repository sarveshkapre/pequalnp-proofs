"""Encode a five-pair grid test with or without a third point input."""
from itertools import combinations
from pathlib import Path
import argparse
import sys

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[1]
sys.path.insert(0, str(WORK))
from circuit_search import Encoder
sys.path.insert(0, str(WORK / "grid/repair_three/tap_positions"))
from line_order import canonicalize

ROWS = (15, 113)  # line 0 shared; private lines 1..3 and 4..6
MASKS = tuple(m for m in range(128) if all((m & r).bit_count() <= 1 for r in ROWS))


def tests(kept):
    base = []
    fault = []
    for q in (False, True):
        for p in range(4):
            for m in range(128):
                if m.bit_count() > 2 or (q and m & 1):
                    continue
                incident = any(p >> i & 1 and m & row for i, row in enumerate(ROWS))
                if not q and (p, m) in kept:
                    base.append((q, p, m, True))
                if not incident and not (q and p == 3):
                    (fault if q else base).append((q, p, m, False))
    # Once q is on it suffices to constrain the maximal legal negatives.
    fault = [row for row in fault if not any(row!=s and row[1] & s[1] == row[1]
             and row[2] & s[2] == row[2] for s in fault)]
    return base + fault + [(True, 3, 0, True)]


def keep_pairs(shape):
    # Two digits per row: common flag present (0/1), number of private flags (0..3).
    kept = set()
    for i, (common, count) in enumerate(zip(shape[::2], shape[1::2])):
        if common == "1":
            kept.add((1 << i, 1))
        for j in range(int(count)):
            kept.add((1 << i, 1 << (1 + 3*i + j)))
    return kept


def shapes(k):
    choices = [(c,n) for c in range(2) for n in range(4)]
    return [f"{a}{b}{c}{d}" for a,b in choices for c,d in choices
            if (a,b) <= (c,d) and a+b+c+d == k]


def emit(path, shape, size, extra):
    kept = keep_pairs(shape)
    rows = [r for r in tests(kept) if extra or not r[0]]
    enc = Encoder(path)
    outputs, specs = [], []
    first_gate = 4 if extra else 3

    def pin():
        selectors = enc.choose(first_gate + len(outputs))
        line_bits = [enc.var() for _ in range(7)]
        for bit in line_bits:
            enc.clause(-bit, selectors[0])
        for row in ROWS:
            for a, b in combinations([i for i in range(7) if row >> i & 1], 2):
                enc.clause(-line_bits[a], -line_bits[b])
        values = []
        for i, (q, p, m, _) in enumerate(rows):
            v = enc.var()
            active = [bit for j,bit in enumerate(line_bits) if m >> j & 1]
            enc.clause(-selectors[0], -v, *active)
            for bit in active:
                enc.clause(-bit, v)
            for j in range(2):
                enc.clause(-selectors[1+j], v if p >> j & 1 else -v)
            if extra:
                enc.clause(-selectors[3], v if q else -v)
            for selector, prev in zip(selectors[first_gate:], outputs, strict=True):
                enc.clause(-selector, -v, prev[i])
                enc.clause(-selector, v, -prev[i])
            values.append(v)
        return (selectors,line_bits), values

    for _ in range(size):
        left, x = pin()
        right, y = pin()
        op = enc.var()
        for j in range(1,len(left[0])):
            enc.clause(-left[0][j], *right[0][j:])
        if specs:
            last = specs[-1][1][0]
            for j in range(first_gate,len(last)):
                enc.clause(-last[j], *right[0][j:])
        z = []
        for a,b in zip(x,y,strict=True):
            v = enc.var()
            enc.clause(-op,-v,a)
            enc.clause(-op,-v,b)
            enc.clause(-op,v,-a,-b)
            enc.clause(op,v,-a)
            enc.clause(op,v,-b)
            enc.clause(op,-v,a,b)
            z.append(v)
        specs.append((left,right,op))
        outputs.append(z)
    kept_masks = [sum(m for p,m in kept if p == 1 << i) for i in range(2)]
    canonicalize(enc,specs,(*ROWS,*kept_masks),7)
    for v, (_,_,_,goal) in zip(outputs[-1],rows,strict=True):
        enc.clause(v if goal else -v)
    enc.finish()
    return rows, specs, enc.variables, enc.clauses


def decode(specs, model, extra):
    wires = []
    start = 4 if extra else 3
    for left,right,op in specs:
        def arg(pin):
            select, bits = pin
            idx, = [i for i,s in enumerate(select) if s in model]
            if idx == 0:
                mask = sum(1 << j for j,b in enumerate(bits) if b in model)
                assert mask in MASKS
                return ("lines",mask)
            return ("point",idx-1) if idx < start else ("gate",idx-start)
        wires.append(("and" if op in model else "or",arg(left),arg(right)))
    return wires


def evaluate(net, q, p, m):
    values = []
    for op,a,b in net:
        def read(pin):
            kind,i = pin
            if kind == "lines":
                return bool(i & m)
            if kind == "point":
                return q if i == 2 else bool(p & (1 << i))
            return values[i]
        x,y = read(a),read(b)
        values.append((x and y) if op == "and" else (x or y))
    return values[-1]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shape", choices=shapes(5))
    parser.add_argument("size",type=int)
    parser.add_argument("path",type=Path)
    parser.add_argument("--extra",action="store_true")
    args = parser.parse_args()
    rows,_,variables,clauses = emit(args.path,args.shape,args.size,args.extra)
    print(f"{len(rows)} tests, {variables} variables, {clauses} clauses")
