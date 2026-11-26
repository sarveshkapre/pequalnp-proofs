"""Compare the searches with brute-force gate-list expansion on four-input truth tables."""
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from cores import HERE, bits, run_solver

def truth_costs():
    raw=tuple(sum(1<<v for v in range(16) if v>>i&1) for i in range(4))
    costs={x:0 for x in raw}
    layers={frozenset(raw)}
    for depth in range(1,6):
        next_layer=set()
        for pool in layers:
            for a,b in combinations(pool,2):
                for value in (a&b,a|b):
                    if value in pool: continue
                    costs.setdefault(value,depth)
                    if depth<5: next_layer.add(pool|{value})
        layers=next_layer
    return costs

def run(binaries):
    costs=truth_costs()
    count=checks=0
    for truth in range(1,65535):
        if any((truth>>v)&1 and not (truth>>(v|s))&1 for v in range(16) for s in bits(15)):
            continue
        support=sum(s for s in bits(15) if any(((truth>>v)^(truth>>(v|s)))&1 for v in range(16)))
        if support.bit_count()<2: continue
        positives=[v for v in range(16) if not v&~support and (truth>>v)&1]
        positives=[x for x in positives if not any(y!=x and y&x==y for y in positives)]
        negatives=[v for v in range(16) if not (v&~support or (truth>>v)&1)]
        negatives=[x for x in negatives if not any(x!=y and x&y==x for y in negatives)]
        cost=costs.get(truth,6)
        for bound in sorted({cost-1,cost}&set(range(1,6))):
            for binary in binaries:
                result=run_solver(positives,negatives,bits(support),bound,binary)
                assert result.splitlines()[-1].startswith("FOUND" if cost<=bound else "EXHAUSTED")
                checks+=1
        count+=1
    print(f"Brute-force truth-table controls: {count} monotone functions, {checks} search verdicts agreed.")

if __name__=="__main__":
    with TemporaryDirectory() as tmp:
        binaries=[]
        for name in ("frontier","crosscheck"):
            exe=Path(tmp)/name
            subprocess.run(["c++","-O3","-std=c++17",HERE/(name+".cpp"),"-o",exe],check=True)
            binaries.append(exe)
        run(binaries)
