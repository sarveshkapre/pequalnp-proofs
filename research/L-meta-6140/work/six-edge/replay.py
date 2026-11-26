"""Replay the 95 certified exclusions for the order-three plane.
Uses the original Boolean encoding and an installed CaDiCaL and Lean.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

REFINEMENTS = {
    "base": (None, -1, False),
    "inactive": (False, -1, False),
    "canonical_inactive": (False, -1, True),
    "active": (True, -1, True),
    "points": (True, 0, True),
    "centre_line": (True, 1, True),
    "other_line": (True, 2, True),
}

N = 26
P = range(13)
adj = [set() for _ in range(N)]
edges = []
for p in P:
    for difference in (0, 1, 3, 9):
        line = 13 + (p - difference) % 13
        adj[p].add(line)
        adj[line].add(p)
        edges.append((p, line))
full = (1 << 13) - 1
line_masks = [sum(1 << (line - 13) for line in adj[p]) for p in P]
neg = []
for points in range(1 << 13):
    lines = full
    for p in P:
        if points >> p & 1:
            lines &= ~line_masks[p]
    if all(points >> p & 1 or line_masks[p] & lines for p in P):
        neg.append(points | (lines << 13))
assert len(neg) == 704
pos = [(1 << p) | (1 << line) for p, line in edges]


class CNF:
    def __init__(self):
        self.n = 1
        self.clauses = [(1,)]

    def new_var(self):
        self.n += 1
        return self.n

    def clause(self, *literals):
        if 1 in literals:
            return
        terms = set(literals) - {-1}
        if any(-lit in terms for lit in terms):
            return
        self.clauses.append(tuple(sorted(terms, key=abs)))

    def disjunction(self, literals):
        terms = tuple(dict.fromkeys(literals))
        if 1 in terms:
            return 1
        terms = tuple(lit for lit in terms if lit != -1)
        if not terms:
            return -1
        if len(terms) == 1:
            return terms[0]
        result = self.new_var()
        self.clause(-result, *terms)
        for lit in terms:
            self.clause(-lit, result)
        return result

    def both(self, literals):
        return -self.disjunction([-lit for lit in literals])

    def one(self, literals):
        self.clause(*literals)
        for i, j in combinations(literals, 2):
            self.clause(-i, -j)

    def dimacs(self):
        header = f"p cnf {self.n} {len(self.clauses)}\n"
        body = "".join(" ".join(map(str, clause)) + " 0\n" for clause in self.clauses)
        return (header + body).encode()

    def exact(self, literals, count):
        # thresholds[i] represents at least i true literals so far.
        thresholds = [1] + [-1] * (count + 1)
        for lit in literals:
            thresholds = [1] + [
                self.disjunction((thresholds[i], self.both((lit, thresholds[i-1]))))
                for i in range(1, count + 2)
            ]
        self.clause(thresholds[count])
        self.clause(-thresholds[count + 1])

def build(order, extra, limitneg, refinement):
    """Compile one gate order and centre-route mask to DIMACS."""
    active, geometry, canonical = REFINEMENTS[refinement]
    K = range(13, 26)
    dead = 6
    cnf=CNF()
    # A leaf can contain only a graph neighbour. Each retained pair
    # comes from the one top at its line.
    leaf=[(z,{i:cnf.new_var() for i in sorted(adj[z])}) for z in K]
    for _,a in leaf:cnf.clause(*a.values())
    retained={}
    for p,l in edges:
        flags=[a[l] for z,a in leaf if z==p]+[a[p] for z,a in leaf if z==l]
        retained[p,l]=cnf.disjunction(flags)
    cnf.exact([-r for r in retained.values()],dead)

    # Under a centered top or a dirty AND, every non-special internal OR with
    # raw inputs is a Lambda gate. Its raw set is included in a chosen leaf.
    # The raw-set candidates here include every possible singleton and subset.
    atomhosts=[{v:1} for v in range(N)]+[a for _,a in leaf]
    if extra==0:cnf.clause(-retained[0,13])
    samples=pos+limitneg
    on=[tuple(v for v in range(N) if x>>v&1) for x in samples]
    sset=[set(s) for s in on]
    stages=[]
    gate_uses=[]
    gate_anc=[]
    port_specs=[]
    center_uses={i:[] for i in range(len(order))}
    def eligible(prev, raw, select):
        cnf.clause(-select,*prev)
        for old,new in zip(prev,raw):cnf.clause(-select,-old,new)
    def port():
        direct=[cnf.new_var() for _ in stages]
        for used,select in zip(gate_uses,direct):used.append(select)
        mode=cnf.new_var()
        cnf.one([mode]+direct)
        atom=[cnf.new_var() for _ in range(N)]
        cnf.clause(-mode,*atom)
        for w in atom:cnf.clause(-w,mode)
        host=[cnf.new_var() for _ in atomhosts]
        for h in host: cnf.clause(-h,mode)
        cnf.clause(-mode,*host)
        for i,j in combinations(host,2):cnf.clause(-i,-j)
        for n,(h,bank) in enumerate(zip(host,atomhosts)):
            for i,b in enumerate(atom):cnf.clause(-h,-b,bank.get(i,-1))
            if n>=N: cnf.clause(-h,*(cnf.both((atom[i],atom[j])) for i,j in combinations(bank,2)))
        read=[]
        for st,(op,raw,vals) in enumerate(stages):
            if op!='O':continue
            x=cnf.new_var()
            cnf.clause(-x,mode)
            eligible(raw,atom,x)
            gate_uses[st].append(x)
            read.append((x,vals))
        port_specs.append((atom,direct,[(q,i) for (q,_),i in zip(read,[i for i,(t,_,_) in enumerate(stages) if t=='O'],strict=True)], [mode]+direct))
        rawout=[cnf.disjunction([a]+[cnf.both([r,raw[v]]) for r,(_,raw,vals) in zip(direct,stages)]) for v,a in enumerate(atom)]
        vals=[]
        for k,A in enumerate(on):
            terms=[atom[v] for v in A]+[cnf.both((r,vs[k])) for r,vs in read]
            terms+=[cnf.both((d,vs[k])) for d,(_,raw,vs) in zip(direct,stages)]
            vals.append(cnf.disjunction(terms))
        anc=[]
        if canonical:
            anc=[cnf.disjunction([cnf.both((d,dr[i])) for d,dr in zip(direct,gate_anc)]
                         +[cnf.both((p,gate_anc[j][i])) for p,j in port_specs[-1][2]])
                 for i in range(len(order))]
        return rawout,vals,anc
    for kind in order:
        ar,av,ac=port(); br,bv,bc=port()
        for i,a in enumerate(port_specs[-2][3]):
            for b in port_specs[-1][3][:i]:
                cnf.clause(-a,-b)
        f=cnf.disjunction if kind=='O' else cnf.both
        val=[f(t) for t in zip(av,bv)]
        raw=[f(t) for t in zip(ar,br)] if kind=='O' else [-1]*N
        if kind=='A' and not stages and geometry>=0:
            left,right=ar,br
            if geometry==0:
                for v in range(13,26):
                    cnf.clause(-left[v]);cnf.clause(-right[v])
            else:
                line=12+geometry
                assert extra!=0 or geometry==1
                for v in range(13,26):cnf.clause(-left[v])
                cnf.clause(right[line])
                cnf.clause(*(left[v] for v in P if v not in adj[line]))
        if active is not None and kind=='A' and len(stages)==order.index('A'):
            witness=[cnf.both((-retained[edge],v)) for edge,v in zip(edges,val[:52],strict=True)]
            if active and extra==0:
                cnf.clause(val[edges.index((0,13))])
            elif active:
                cnf.clause(*witness)
            else:
                for w in witness:cnf.clause(-w)
                # On retained edges the raw stars already suffice. On the other
                # positive edges this signal was false before the substitution.
                val=[-1]*len(val)
        ix=len(stages)
        anc=[]
        if canonical:
            if kind=='A':
                anc=[1 if j==ix else -1 for j in range(len(order))]
            else:
                anc=[cnf.disjunction((a,b)) for a,b in zip(ac,bc)]
                if ix>order.index('A'):
                    # A raw-only OR can be scheduled before all dirty ANDs.
                    cnf.clause(*anc)
                if geometry==0 and extra>>ix&1:
                    cnf.clause(-anc[0])
        stages.append((kind,raw,val))
        gate_anc.append(anc)
        gate_uses.append([])
    answers=[[] for _ in on]
    for z,row in leaf:
        rawL=[row.get(v,-1) for v in range(N)]
        rawZ=[1 if z==v else -1 for v in range(N)]
        zread=[];lread=[]
        for idx,(kind,raw,val) in enumerate(stages):
            if kind!='O' or idx<order.index('A'):continue
            iz,il=cnf.new_var(),cnf.new_var()
            gate_uses[idx].extend((iz,il))
            eligible(raw,rawZ,iz);eligible(raw,rawL,il)
            if extra>>idx&1:
                center_uses[idx].append(iz)
                if idx==(extra&-extra).bit_length()-1 and z==13:
                    cnf.clause(iz)
            else:
                cnf.clause(-iz)
            zread.append((iz,val));lread.append((il,val))
        for k,A in enumerate(on):
            c=1 if z in sset[k] else cnf.disjunction([cnf.both((x,vs[k])) for x,vs in zread])
            d=cnf.disjunction([row[v] for v in A if v in row]+[cnf.both((x,vs[k])) for x,vs in lread])
            hit=cnf.both((c,d))
            if k<52:answers[k].append(hit)
            else:cnf.clause(-hit)
    for k in range(52):cnf.clause(*answers[k])
    for idx,(kind,uses) in enumerate(zip(order,gate_uses)):
        if kind=='A':cnf.clause(*uses)
        if extra>>idx&1:cnf.clause(*center_uses[idx])
    return cnf.dimacs()

def greedy():
    slots={}
    sets=[]
    for x in neg:
        active=[v for v in range(N) if x>>v&1]
        bits=0
        for k in (1,2,3,4):
            for q in combinations(active,k):
                idx=slots.setdefault(q,len(slots))
                bits|=1<<idx
        sets.append(bits)
    unused=(1<<len(slots))-1
    picks=[]; available=set(range(len(neg)))
    while unused:
        best=max(available,key=lambda i:((sets[i]&unused).bit_count(),-i))
        unused &= ~sets[best]
        picks.append(neg[best]);available.remove(best)
    return picks+[neg[j] for j in sorted(available)]

def formula_from_trace(row, negatives, directory):
    order, mask, refinement, fingerprint = row
    formula = (directory / f"{order}-{mask}-{refinement}.cnf").read_bytes()
    if formula != build(order, mask, negatives, refinement):
        raise ValueError(f"{order}/{mask}/{refinement} Lean CNF differs from the original encoder")
    digest = sha256(formula).hexdigest()
    if digest != fingerprint:
        raise ValueError(f"{order}/{mask}/{refinement} formula changed: {digest}")
    return formula


def replay_case(row, formula, solver, lean, checker):
    order, mask, refinement, fingerprint = row
    solved = run([solver, "-q", "--lrat", "--no-binary", "-", "-"],
                 input=formula, capture_output=True, check=False)
    if solved.returncode != 20:
        raise ValueError(f"{order}/{mask}/{refinement} solver returned {solved.returncode}")
    trace = b"\n".join(line for line in solved.stdout.splitlines() if line[:1].isdigit())
    with TemporaryDirectory(prefix="plane-six-certificate-") as temp:
        proof = Path(temp) / "proof.lrat"
        (Path(temp) / "case.txt").write_text(f"{order} {mask} {refinement}\n")
        proof.write_bytes(trace + b"\n")
        result = run([lean, str(checker)], cwd=temp, text=True, capture_output=True)
        if result.returncode:
            raise ValueError(f"{order}/{mask}/{refinement} failed: {result.stdout}{result.stderr}")
    print(f"{order} {mask:02d} {refinement} {fingerprint} {result.stdout.strip()}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cadical", required=True)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    rows = json.loads((directory / "certificates.json").read_text())
    declared = run([args.lean, "--run", str(directory / "SixEdgeCertificates.lean")],
                   text=True, capture_output=True, check=True)
    keys = [f"{order} {mask} {refinement}" for order, mask, refinement, _ in rows]
    if declared.stdout.splitlines() != keys:
        raise ValueError("certificate manifest does not match the 95 Lean case keys")
    negatives = greedy()[:80]
    with TemporaryDirectory(prefix="plane-six-formulas-") as temp:
        formulas = Path(temp)
        checker = formulas / "CheckRecordedCase.lean"
        checker.write_text("import SixEdgeJointReplay\n#eval SixEdge.Formula.replayRecordedCase\n")
        export = formulas / "ExportFormulas.lean"
        export.write_text("import SixEdgeTrace\nset_option maxRecDepth 100000 in\n"
                          "set_option maxHeartbeats 0 in\n"
                          f"#eval SixEdge.Formula.writeReplayInputs {json.dumps(str(formulas))}\n")
        run([args.lean, str(export)], check=True)
        def verify(row):
            formula = formula_from_trace(row, negatives, formulas)
            replay_case(row, formula, args.cadical, args.lean, checker)

        with ThreadPoolExecutor(max_workers=args.jobs) as workers:
            list(workers.map(verify, rows))


if __name__ == "__main__":
    main()
