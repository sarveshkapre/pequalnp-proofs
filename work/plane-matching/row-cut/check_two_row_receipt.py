"""Regenerate the CNFs in scratch space and check the bundled LRAT proofs offline."""
from pathlib import Path
import argparse
import json
import subprocess
from tempfile import TemporaryDirectory

from replay_two_rows import digest
from two_rows_sat import WORK, emit, evaluate, shapes


def check(evidence, lean):
    receipt = json.loads((evidence/"receipt.json").read_text())
    proofs = actions = controls = 0
    with TemporaryDirectory() as scratch:
        for shape in shapes(5):
            for extra in (False,True):
                name = ("third-point" if extra else "ordinary")+"-"+shape
                for control in (False,True):
                    key = name + ("-control" if control else "")
                    rec = receipt[key]
                    path = Path(scratch)/(key+".cnf")
                    rows,_,variables,clauses = emit(path,shape,(7 if extra else 5)+int(control),extra)
                    assert (variables,clauses,len(rows),digest(path)) == (
                        rec["variables"],rec["clauses"],rec["tests"],rec["formula"])
                    if control:
                        net = rec["control_circuit"]
                        assert len(net)==(8 if extra else 6)
                        assert all(evaluate(net,q,p,m)==target for q,p,m,target in rows)
                        controls+=1
                    else:
                        proof = evidence/(name+".lrat")
                        assert digest(proof)==rec["proof"]
                        replay = subprocess.run([lean,"--run",WORK/"grid/bounds/CheckCover.lean",path,proof],
                                                capture_output=True,text=True,check=True)
                        assert replay.stdout.strip() == rec["checked"]
                        proofs+=1
                        actions+=int(replay.stdout.split()[-2])
    assert len(receipt)==24 and proofs==controls==12
    print(f"{proofs} checked contradictions, {actions:,} LRAT actions, {controls} evaluated one-gate-larger controls.")


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("evidence", type=Path)
    p.add_argument("--lean",type=Path,default=Path.home()/".elan/toolchains/leanprover--lean4---v4.36.0/bin/lean")
    a=p.parse_args()
    check(a.evidence,a.lean)
