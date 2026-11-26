"""Project the original 177 tests, enumerate the available line sources, and run the small-core search."""
from argparse import ArgumentParser
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
TABLE = HERE.parents[2] / "grid/search/cases.txt"
ROWS = (29, 225, 1793, 294, 586, 1170)
BANK = (3, 40, 1064, 272, 336, 516, 644, 48, 560, 264, 392, 68, 1092)

def bits(m):
    return [1 << j for j in range(m.bit_length()) if m >> j & 1]

def physical_tests():
    entries = [tuple(map(int, line.split())) for line in TABLE.read_text().splitlines()]
    assert len(entries)==177 and all(y in (0,1) for _,y in entries)
    for x,_ in entries:
        lines=(x>>6)&2047
        assert x>>17 == sum(1<<i for i,m in enumerate(BANK) if m & lines)
    plus = {x % 2**17 for x,y in entries if y}
    minus = {x % 2**17 for x,y in entries if not y}
    assert len(plus) == 24 and len(minus) == 153
    assert plus == {1 << r | l << 6 for r,row in enumerate(ROWS) for l in bits(row)}
    return plus, minus

def geometry(rows):
    points = sum(1 << r for r in rows)
    union = 0
    for r in rows:
        union |= ROWS[r]
    core = sum(l for l in bits(union) if sum(bool(ROWS[r] & l) for r in rows) >= 2)
    masks = set(bits(union)) | {m & union for m in BANK}
    for r,lines in enumerate(ROWS):
        if r not in rows:
            masks.update(m & union for m in range(2048) if m & ~lines == 0)
    return points, union, core, sorted(masks - {0})

def projected(points, lines):
    plus, minus = physical_tests()
    allowed = points | (lines << 6)
    pos = sorted(x for x in plus if not x & ~allowed)
    neg = {x & allowed for x in minus}
    maxima = sorted(x for x in neg if not any(x != y and x & y == x for y in neg))
    assert all(x & y != x for x in pos for y in maxima)
    return pos, maxima

def solve(rows, size, solver, optional, keep=None):
    points, _, core, masks = geometry(rows)
    lines = core if keep is None else keep
    points = sum(1<<r for r in rows if ROWS[r] & lines)
    pos, neg = projected(points, lines)
    extra = sorted({m & lines for m in masks if (m & lines).bit_count()>1})
    sources = bits(points) + [m << 6 for m in bits(lines)]
    sources.extend(m << 6 for i,m in enumerate(extra) if optional>>i & 1)
    assert optional < (1<<len(extra))
    return run_solver(pos, neg, sources, size, solver)

def run_solver(pos, neg, sources, size, solver):
    data = [f"{len(pos)} {len(neg)} {len(sources)} {size}"]
    for m in sources:
        accepts = sum(1<<i for i,x in enumerate(pos) if x & m)
        rejects = sum(1<<i for i,x in enumerate(neg) if not x & m)
        data.append(f"{accepts} {rejects % (1<<64)} {rejects >> 64}")
    result = subprocess.run([solver],input="\n".join(data),capture_output=True,text=True,check=True)
    records = result.stdout.splitlines()
    if records[-1].startswith("FOUND"):
        for target, tests in [(True,pos),(False,neg)]:
            for x in tests:
                values = [bool(x & m) for m in sources]
                for line in records[:-1]:
                    op,a,b = line.split()
                    left,right=values[int(a)],values[int(b)]
                    assert op in ("and","or")
                    values.append(left and right if op=="and" else left or right)
                assert values[-1] == target
    return result.stdout

if __name__ == "__main__":
    p=ArgumentParser(description=__doc__)
    p.add_argument("solver",type=Path)
    p.add_argument("rows",help="Indices of the four active rows, e.g. 0123")
    p.add_argument("size",type=int)
    p.add_argument("optional",type=int,default=0,nargs="?")
    p.add_argument("--lines",type=int)
    opt=p.parse_args()
    print(solve(tuple(map(int,opt.rows)),opt.size,opt.solver.resolve(),opt.optional,opt.lines),end="")
