"""Replay the two seven-gate exclusions and check their physical projections."""
from argparse import ArgumentParser
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory
import os
import subprocess

from three_rows_core import TARGET, encode, samples
from three_rows_sources import ROWS, bits, lean_data
from cases import cases

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[1]
HASHES = {
    "common": ("f3f161987455618e00b6c6ac6a35d7f8caff19ea4c41feaacdde640ee70d69d2",
               "656b37438452ace36490a8a51ec2a69fb3cefdbba8a18ca4923a650e678b8c0a"),
    "triangle": ("abb6429d4f57f86969f41e8bb33bc2f0f5b2124d298b2ff01a76900fbe14a821",
                 "be2180bf60dd80df6a35823d1b5c9254a5461c40c366318346aa85f00b05c2dd"),
}


def check_physical():
    # Decode the original 30-wire boundary table, separately from the row masks.
    published = {}
    for record in (WORK/"grid/search/cases.txt").read_text().splitlines():
        mask, label = map(int, record.split())
        published[mask & ((1 << 17)-1)] = label
    assert len(published) == 177 and sum(published.values()) == 24
    assert published == {p | m << 6: y for p,m,y in cases()}
    negatives = [v for v,y in published.items() if not y]
    shapes = {"common": 0, "triangle": 0}
    projections = 0
    for rows in combinations(range(6),3):
        a,b,c = (ROWS[r] for r in rows)
        shared = a & b & c
        if shared:
            shape = "common"
            choices = ((shared, *singletons) for singletons in
                       product(*(bits(row & ~shared) for row in (a,b,c))))
        else:
            shape = "triangle"
            choices = [(a&b, a&c, b&c)]
        for lines in choices:
            assert all(l.bit_count() == 1 for l in lines) and len(set(lines)) == len(lines)
            pattern = tuple(sum(1<<j for j,l in enumerate(lines) if row&l) for row in (a,b,c))
            assert pattern == TARGET[shape]
            for p,m,wanted in samples(pattern):
                point = sum(1<<r for i,r in enumerate(rows) if p>>i & 1)
                line = sum(l for i,l in enumerate(lines) if m>>i & 1)
                mask = point | line << 6
                if wanted:
                    assert published.get(mask) == 1
                else:
                    assert any(mask & n == mask for n in negatives)
                projections += 1
            shapes[shape] += 1
    assert shapes == {"common":54, "triangle":18}
    # Independently evaluate the explicit 29-gate control on every physical input.
    gates = []
    def gate(is_and, a, b):
        gates.append((is_and,a,b))
        return 29 + len(gates)
    terms = []
    for r,row in enumerate(ROWS):
        a,b,c,d = (5 + l.bit_length() for l in bits(row))
        left = gate(False,a,b)
        right = gate(False,c,d)
        terms.append(gate(True,r,gate(False,left,right)))
    out = terms[0]
    for other in terms[1:]:
        out = gate(False,out,other)
    width = 1<<17
    all_ones = (1<<width)-1
    inputs = []
    for i in range(17):
        step = 1<<i
        inputs.append((all_ones // ((1<<(2*step))-1)) * ((1<<step)-1) << step)
    # Supplied ORs are unused in this particular control.
    wires = inputs + [0]*13
    for is_and,a,b in gates:
        wires.append(wires[a]&wires[b] if is_and else wires[a]|wires[b])
    assert len(gates) == 29 and out == 58
    target = sum(1<<x for x in range(width) if any(
        x>>r & 1 and (x>>6)&row for r,row in enumerate(ROWS)))
    assert wires[out] == target
    print(f"{projections} signed physical projections across 72 embeddings; 29-gate control passed all {width} inputs.")


def check_control(model, wiring, shape):
    ones = {int(v) for row in model.splitlines() if row.startswith("v ")
            for v in row.split()[1:] if int(v)>0}
    gates = []
    for left,right,op in wiring:
        a, = [i for i,v in enumerate(left) if v in ones]
        b, = [i for i,v in enumerate(right) if v in ones]
        gates.append((op in ones,a,b))
    for p,m,label in samples(TARGET[shape]):
        raw = p | m<<3
        wires = [bool(raw >> i & 1) for i in range(3+max(TARGET[shape]).bit_length())]
        for is_and,a,b in gates:
            wires.append((wires[a] and wires[b]) if is_and else (wires[a] or wires[b]))
        assert wires[-1] == label


def replay(evidence, binary):
    assert subprocess.check_output([binary/"lean","--version"],text=True).startswith("Lean (version 4.36.0,")
    assert lean_data() == (HERE/"ThreeRowData.lean").read_text()
    check_physical()
    with TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        env = dict(os.environ, LEAN_PATH=tmp, PATH=str(binary)+os.pathsep+os.environ["PATH"])
        for module in ("ThreeRowData","ThreeRowSources"):
            subprocess.run([binary/"lean","-DwarningAsError=true","-R",HERE,"-o",
                            scratch/(module+".olean"),HERE/(module+".lean")],env=env,check=True)
        subprocess.run([binary/"leanchecker","ThreeRowSources"],env=env,cwd=scratch,check=True)
        for shape,(cnf_hash,proof_hash) in HASHES.items():
            cnf = scratch/(shape+".cnf")
            encode(cnf,shape,7)
            proof = evidence/(shape+"7.lrat")
            assert sha256(cnf.read_bytes()).hexdigest() == cnf_hash
            assert sha256(proof.read_bytes()).hexdigest() == proof_hash
            subprocess.run([binary/"lean","--run",WORK/"grid/bounds/CheckCover.lean",cnf,proof],
                           env=env,check=True)
            wiring = encode(cnf,shape,8)
            result = subprocess.run([binary/"cadical","-q",cnf],capture_output=True,text=True)
            assert result.returncode == 10
            check_control(result.stdout,wiring,shape)
            print(f"{shape}: decoded eight-gate control passed")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("evidence",type=Path)
    parser.add_argument("--bin",type=Path,
                        default=Path.home()/".elan/toolchains/leanprover--lean4---v4.36.0/bin")
    args = parser.parse_args()
    replay(args.evidence.resolve(),args.bin.resolve())
