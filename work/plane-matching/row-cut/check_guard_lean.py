"""Compile the guard proofs and replay the resulting module with Lean's kernel."""
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import os
import subprocess


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("lean_project",type=Path,help="built Lean project with the pinned Mathlib dependency")
    p.add_argument("--bin",type=Path,default=Path.home()/".elan/toolchains/leanprover--lean4---v4.36.0/bin")
    a=p.parse_args()
    lean=a.bin/"lean"
    assert subprocess.check_output([lean,"--version"],text=True).startswith("Lean (version 4.36.0,")
    lake=a.lean_project.resolve()/".lake"
    libs=[lake/"build/lib/lean",*sorted((lake/"packages").glob("*/.lake/build/lib/lean"))]
    source=Path(__file__).resolve().parent
    with TemporaryDirectory() as scratch:
        env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[scratch,*libs])),LEAN_NUM_THREADS="2",
                 PATH=os.pathsep.join([str(a.bin.resolve()),os.environ.get("PATH","")]))
        for module in ("RowPartition","GateLedger","GuardRestriction"):
            subprocess.run([lean,"-DwarningAsError=true","-R",source,"-o",Path(scratch)/(module+".olean"),
                            source/(module+".lean")],env=env,check=True)
        subprocess.run([a.bin/"leanchecker","-v","GuardRestriction"],env=env,cwd=scratch,check=True)
