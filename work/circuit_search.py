"""Reproduce the finite tests for L-meta-2216 and search for a smaller circuit."""
import argparse
import itertools
import json
from pathlib import Path
import random

POINTS, LINES = 12, 13
INPUTS = POINTS + LINES
SPECIAL = (12, 13, 15, 21)
ROWS = [tuple(j for j in range(POINTS, INPUTS) if (i+j+2) % 13 in (0,1,3,9))
        for i in range(POINTS)]
def bitset(values):
    return sum(1 << i for i in values)
AUX = bitset(SPECIAL)
NEIGHBORS = [bitset(r) for r in ROWS]

def maximal_independent(allowed):
    """Choose a point set, take all available non-neighbors, then close the point set."""
    for points in range(1 << POINTS):
        lines = allowed
        for i, nb in enumerate(NEIGHBORS):
            if points >> i & 1:
                lines &= ~nb
        if points == bitset(i for i, nb in enumerate(NEIGHBORS) if not lines & nb):
            yield points | lines

def tests():
    want = {}
    def add(x, main, aux=None):
        if x in want:
            m, a = want[x]
            assert m == main and (a is None or aux is None or a == aux)
            if aux is None: aux = a
        want[x] = (main, aux)
    for i, row in enumerate(ROWS):
        for j in row: add((1 << i) | (1 << j), True)
    for j in SPECIAL: add(1 << j, False, True)
    all_lines = bitset(range(POINTS, INPUTS))
    for x in maximal_independent(all_lines): add(x, False, bool(x & AUX))
    for x in maximal_independent(all_lines & ~AUX): add(x, False, False)
    return want

def star():
    gates = []
    def gate(op, a, b):
        gates.append((op, a, b))
        return INPUTS+len(gates)-1
    def join(ws):
        x, *tail = ws
        for y in tail: x = gate('or', x, y)
        return x
    products = [gate('and', i, join(row)) for i,row in enumerate(ROWS)]
    return gates, join(products), join(SPECIAL)

def signatures(rows):
    return [bitset(i for i, x in enumerate(rows) if x >> w & 1) for w in range(INPUTS)]

def evaluate(inputs, gates):
    wires = inputs.copy()
    for op,a,b in gates:
        wires.append(wires[a] & wires[b] if op=='and' else wires[a] | wires[b])
    return wires

def deletion_search(wanted):
    # Bypass any one gate to any earlier wire on all of its fanouts, including outputs.
    rows = list(wanted)
    inputs = signatures(rows)
    mask = (1<<len(rows)) - 1
    primary = bitset(i for i,x in enumerate(rows) if wanted[x][0])
    aux_yes = bitset(i for i,x in enumerate(rows) if wanted[x][1] is True)
    aux_no = bitset(i for i,x in enumerate(rows) if wanted[x][1] is False)
    gates, out, aux = star()
    base = evaluate(inputs,gates)
    assert len(gates)==62 and base[out]==primary and (base[aux]&aux_yes)==aux_yes and not (base[aux]&aux_no)
    def fails(w): return ((w & aux_no) | ((mask ^ w) & aux_yes)).bit_count()
    best = len(rows)+1
    count = 0
    for g, (op,a,b) in enumerate(gates):
        k = INPUTS+g
        for old in range(k):
            w = base[:k] + [base[old]]
            for op,a,b in gates[g+1:]: w.append(w[a] & w[b] if op=='and' else w[a] | w[b])
            # The two output indices can both be chosen afresh after each bypass.
            missing_main = min((v ^ primary).bit_count() for v in w)
            missing_aux = min(map(fails,w))
            best = min(best, missing_main+missing_aux)
            count += 1
    return {'tests':len(rows),'62_gate_control':'passed','61_gate_bypasses':count,'best_failed_output_checks':best}

class Encoder:
    """Construct a relaxation that includes every circuit in the assigned model."""
    def __init__(self,path):
        self.path=path
        self.body=path.with_suffix('.body')
        self.f=self.body.open('w')
        self.variables=self.clauses=0
    def var(self):
        self.variables+=1
        return self.variables
    def clause(self,*lits):
        self.f.write(' '.join(map(str,lits))+' 0\n')
        self.clauses+=1
    def choose(self,n):
        xs=[self.var() for _ in range(n)]
        self.clause(*xs)
        prev=None
        for x in xs[:-1]:
            nxt=self.var()
            self.clause(-x,nxt)
            if prev: self.clause(-prev,nxt); self.clause(-x,-prev)
            prev=nxt
        if prev: self.clause(-xs[-1],-prev)
        return xs
    def finish(self):
        import shutil
        self.f.close()
        with self.path.open('wb') as dst,self.body.open('rb') as src:
            dst.write(f'p cnf {self.variables} {self.clauses}\n'.encode())
            shutil.copyfileobj(src,dst)
        self.body.unlink()
    def mux(self,selectors, row):
        y=self.var()
        for s,x in zip(selectors,row,strict=True):
            self.clause(-s,-x,y)
            self.clause(-s,x,-y)
        return y

def encode(path,wanted,n_gates,nsamples,control,canonical=False):
    positive=[x for x,(m,_) in wanted.items() if m]
    rest=[x for x in wanted if x not in positive and x.bit_count()>1]
    set_seed=random.Random(2216)
    set_seed.shuffle(rest)
    samples=(positive+[1<<j for j in SPECIAL]+rest)[:nsamples]
    enc=Encoder(path)
    one=enc.var(); enc.clause(one)
    rows=[[one if x>>i&1 else -one for i in range(INPUTS)]+[-one,one] for x in samples]
    model, main, aux=star()
    def shift(j): return j if j<INPUTS else j+2
    uses=[[] for _ in range(INPUTS)]
    last_b=[]
    pos=[-one]*POINTS+[one]*LINES+[-one,-one]
    nonlinear=[-one]*len(pos)
    def disj(*vs):
        y=enc.var()
        for v in vs: enc.clause(-v,y)
        enc.clause(-y,*vs)
        return y
    def conj(*vs): return -disj(*[-v for v in vs])
    if control and canonical:
        # Topologically canonical reorder of the planted DAG, excluding the two virtual constants.
        numbering={i:i for i in range(INPUTS)}
        pending=set(range(n_gates)); ordered=[]
        while pending:
            candidates=[(max(numbering[model[k][1]],numbering[model[k][2]]),
                         min(numbering[model[k][1]],numbering[model[k][2]]),k)
                        for k in pending if model[k][1] in numbering and model[k][2] in numbering]
            r,l,k=min(candidates); op=model[k][0]; pending.remove(k)
            numbering[INPUTS+k]=INPUTS+len(ordered);ordered.append((op,l,r))
        main,aux=numbering[main],numbering[aux];model=ordered
    for i in range(n_gates):
        a=enc.choose(len(rows[0])); b=enc.choose(len(rows[0])); op=enc.var()
        # Binary gates may take equal operands, and either constant, including missing wires.
        # Commutativity permits selecting operands in nondecreasing order.
        for j in range(1,len(a)):
            for k in range(j): enc.clause(-a[j],-b[k])
        if canonical:
            for j in (INPUTS,INPUTS+1): enc.clause(-a[j]);enc.clause(-b[j])
            for j in range(len(a)): enc.clause(-a[j],-b[j])
            for j in range(INPUTS): uses[j].extend([a[j],b[j]])
            # A topological renumbering can process gates in order of their last available operand.
            for j,old in enumerate(last_b):
                if j: enc.clause(-old,*b[j:])
            last_b=b
            la,lb=enc.mux(a,pos),enc.mux(b,pos)
            na,nb=enc.mux(a,nonlinear),enc.mux(b,nonlinear)
            pos.append(disj(la,lb)); nonlinear.append(disj(na,nb,conj(op,la,lb)))
        if control:
            g,left,right=model[i]
            l,r=sorted((shift(left),shift(right)))
            enc.clause(a[l]);enc.clause(b[r]);enc.clause(op if g=='and' else -op)
        for row in rows:
            l,r=enc.mux(a,row),enc.mux(b,row)
            y=enc.var()
            enc.clause(-op,-y,l);enc.clause(-op,-y,r);enc.clause(-op,-l,-r,y)
            enc.clause(op,-l,y);enc.clause(op,-r,y);enc.clause(op,-y,l,r)
            row.append(y)
    if canonical:
        for occurrences in uses: enc.clause(*occurrences)
    selected_nonlin=[]
    for index,out in enumerate([main,aux]):
        sels=enc.choose(len(rows[0]))
        if canonical: selected_nonlin.append(enc.mux(sels,nonlinear))
        if control: enc.clause(sels[shift(out)])
        for x,row in zip(samples,rows,strict=True):
            val=wanted[x][index]
            if val is not None: enc.clause(enc.mux(sels,row) if val else -enc.mux(sels,row))
    if canonical and n_gates<=61: enc.clause(*selected_nonlin)
    enc.finish()
    print('encoded',len(samples),'inputs',n_gates,'gates',enc.variables,'vars',enc.clauses,'clauses',flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--cnf',type=Path)
    ap.add_argument('--gates',type=int,default=61)
    ap.add_argument('--samples',type=int,default=128)
    ap.add_argument('--control',action='store_true')
    ap.add_argument('--canonical',action='store_true')
    args=ap.parse_args()
    w=tests()
    if args.cnf: encode(args.cnf,w,args.gates,args.samples,args.control,args.canonical)
    else: print(json.dumps(deletion_search(w),indent=2))
