"""Independently reconstruct the physical constraints and certify that no source set was missed."""
from argparse import ArgumentParser
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess

from cores import BANK, HERE, ROWS, physical_tests
from sources import survivors

def physical():
    positives, boundary = physical_tests()
    negatives = {p | l<<6 for l in range(2048)
                 if all((m & l).bit_count()<=2 for m in (*ROWS,*BANK))
                 for p in range(64) if p&7!=7 and p&56!=56
                 and all(not (p>>i&1 and l&r) for i,r in enumerate(ROWS))}
    maximal = {n for n in negatives if all((n | 1<<i) not in negatives
               for i in range(17) if not n>>i&1)}
    assert maximal==boundary and len(negatives)==1072
    return positives, negatives

def instance(rs, positives, negatives):
    active = set(rs)
    lines = [[i for i,row in enumerate(ROWS) if row&(1<<l)] for l in range(11)]
    keep = sum(1<<l for l,pts in enumerate(lines) if active & set(pts))
    central = sum(1<<l for l,pts in enumerate(lines) if len(active & set(pts))>1)
    candidates={1<<l for l in range(11)} | set(BANK)
    for i,row in enumerate(ROWS):
        if i in active: continue
        ls=[1<<l for l in range(11) if row>>l&1]
        for width in range(2,5):
            candidates.update(map(sum,combinations(ls,width)))
    bank=sorted({c&keep for c in candidates}-{0})
    domain=sum(1<<r for r in rs) | keep<<6
    # Use every single-point negative and every signed flag, independent of
    # maximal projection or the inclusion-minimal hitting clauses in sources.py.
    required=set()
    for a in positives:
        if a & ~domain: continue
        for b in negatives:
            if b & ~domain or a&63 != b&63: continue
            required.add(tuple(i+1 for i,w in enumerate(bank) if w&(a>>6) and not w&(b>>6)))
    bank2, remaining=survivors(rs)
    assert bank2==bank
    for sel in remaining:
        assert all(any(sel>>(i-1)&1 for i in clause) for clause in required)
    specs=sorted(required)
    top=len(bank)
    def cap(ids,k):
        nonlocal top
        previous=[]
        for i in ids:
            counters=list(range(top+1,top+min(k+1,len(previous)+1)+1))
            top+=len(counters)
            specs.append((-i,counters[0]))
            for j,v in enumerate(previous):
                specs.append((-v,counters[j]))
                if j+1<len(counters):
                    specs.append((-i,-v,counters[j+1]))
            previous=counters
        if len(previous)>k: specs.append((-previous[k],))
    cap(range(1,len(bank)+1),15)
    cap([i+1 for i,w in enumerate(bank) if not w&central],6 if central.bit_count()==4 else 3)
    for used in sorted(remaining):
        specs.append(tuple(-(i+1) if used>>i&1 else i+1 for i in range(len(bank))))
    return (f"p cnf {top} {len(specs)}\n"+
            "".join(" ".join(map(str,clause))+" 0\n" for clause in specs))

def audit(binary, evidence, saved=None):
    positives,negatives=physical()
    checker=HERE.parents[2]/"grid/bounds/CheckCover.lean"
    actions=0
    for rs in combinations(range(6),4):
        name="".join(map(str,rs))
        cnf=evidence/f"{name}.cnf"
        lrat=(saved or evidence)/f"{name}.lrat"
        cnf.write_text(instance(rs,positives,negatives))
        if saved is None:
            result=subprocess.run([binary/"cadical","-q","--lrat","--no-binary",cnf,lrat],
                                  capture_output=True,check=False)
            assert result.returncode==20
        label=subprocess.check_output([binary/"lean","--run",checker,cnf,lrat],text=True).strip()
        actions+=int(label.split()[-2])
        print(name,sha256(cnf.read_bytes()).hexdigest(),sha256(lrat.read_bytes()).hexdigest(),label,flush=True)
    print(f"All 15 source-set completeness certificates verified; {actions} LRAT actions.")

if __name__=="__main__":
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--bin",type=Path,default=Path.home()/".elan/toolchains/leanprover--lean4---v4.36.0/bin")
    mode=cli.add_mutually_exclusive_group()
    mode.add_argument("--evidence",type=Path,help="generate fresh certificates in this directory")
    mode.add_argument("--replay",type=Path,help="check existing certificates without invoking a SAT solver")
    args=cli.parse_args()
    if args.evidence:
        args.evidence.mkdir(parents=True,exist_ok=True)
        audit(args.bin.resolve(),args.evidence.resolve())
    else:
        with TemporaryDirectory() as tmp:
            audit(args.bin.resolve(),Path(tmp),args.replay.resolve() if args.replay else None)
