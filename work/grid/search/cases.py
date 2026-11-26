"""Exhaustive boundary evaluator for the six-point grid."""
from pathlib import Path
ROWS = [29, 225, 1793, 294, 586, 1170]
BANK = [3, 40, 1064, 272, 336, 516, 644, 48, 560, 264, 392, 68, 1092]

def allowed(p, w):
    return p & 7 != 7 and p & 56 != 56 and all((w & q).bit_count() <= 2 for q in ROWS + BANK) and all(not (p & (1 << i)) or not (w & r) for i,r in enumerate(ROWS))

def bank(p, w):
    return p | (w << 6) | sum(bool(w & q) << (17+i) for i,q in enumerate(BANK))

def cases():
    positives = [(1 << i,1 << j,1) for i,r in enumerate(ROWS) for j in range(11) if (r >> j) & 1]
    negatives = {p | (w << 6) for w in range(2048) if all((w & q).bit_count() <= 2 for q in ROWS+BANK) for p in range(64) if allowed(p,w)}
    maximal = sorted(mask for mask in negatives if all(mask | (1 << i) not in negatives for i in range(17) if not(mask & (1<<i))))
    return positives + [(x&63,x>>6,0) for x in maximal]

def read_net(path):
    return [(op,int(a),int(b)) for op,a,b in (l.split() for l in Path(path).read_text().splitlines())]

def verify(gates,detail=True):
    failures=[]
    for p,w,label in cases():
        v=bank(p,w)
        for i,(op,a,b) in enumerate(gates,30):
            assert a<i and b<i and op in ('and','or')
            x,y=(v>>a)&1,(v>>b)&1
            v|=((x&y) if op=='and' else (x|y))<<i
        if (v>>(29+len(gates)))&1 != label:
            failures.append((p,w,label))
    if detail: print(f'{len(gates)} gates, {len(failures)} failures: {failures[:8]}')
    return failures

if __name__=='__main__':
    import sys
    if sys.argv[1]=='write':
        Path(__file__).with_name('cases.txt').write_text(''.join(f'{bank(p,w)} {y}\n' for p,w,y in cases()))
    else: verify(read_net(sys.argv[1]))
