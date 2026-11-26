"""Replay the twelve five-pair exclusions and controls. Requires Lean 4.36.0."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from pathlib import Path
import argparse
import json
import subprocess

from two_rows_sat import WORK, decode, emit, evaluate, shapes


def digest(path):
    with path.open("rb") as f:
        h = sha256()
        for part in iter(lambda: f.read(1 << 20), b""):
            h.update(part)
        return h.hexdigest()


def replay(out, bin_dir, shape, extra):
    size = 7 if extra else 5
    name = ("third-point" if extra else "ordinary") + "-" + shape
    results = {}
    for control in (False, True):
        prefix = name + ("-control" if control else "")
        problem = out / (prefix + ".cnf")
        rows,specs,nvars,nclauses = emit(problem,shape,size+int(control),extra)
        proof = out / (prefix + ".lrat")
        cmd = [bin_dir / "cadical","-q"]
        cmd += [problem] if control else ["--lrat","--no-binary",problem,proof]
        result = subprocess.run(cmd,capture_output=True,text=True)
        record = dict(variables=nvars,clauses=nclauses,formula=digest(problem),tests=len(rows))
        if control:
            assert result.returncode == 10, result.stdout[:300]
            model = {int(i) for line in result.stdout.splitlines() if line.startswith("v ")
                     for i in line.split()[1:]}
            net = decode(specs,model,extra)
            assert all(evaluate(net,q,p,m)==want for q,p,m,want in rows)
            record["control_circuit"] = net
        else:
            assert result.returncode == 20, result.stdout[:300]
            check = subprocess.run([bin_dir / "lean","--run",WORK / "grid/bounds/CheckCover.lean",
                                    problem,proof],capture_output=True,text=True,check=True)
            record.update(proof=digest(proof),checked=check.stdout.strip())
        results[prefix] = record
        print(prefix,record.get("checked","decoded positive control"),flush=True)
    return results


if __name__=="__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("out",type=Path)
    p.add_argument("--bin",type=Path,default=Path.home()/".elan/toolchains/leanprover--lean4---v4.36.0/bin")
    p.add_argument("--jobs",type=int,default=1)
    a = p.parse_args()
    a.out.mkdir(exist_ok=True,parents=True)
    tasks = [(s,b) for s in shapes(5) for b in (False,True)]
    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        records = list(pool.map(lambda t: replay(a.out,a.bin,*t),tasks))
    (a.out/"receipt.json").write_text(json.dumps({k:v for row in records for k,v in row.items()},
                                                   indent=2,sort_keys=True)+"\n")
