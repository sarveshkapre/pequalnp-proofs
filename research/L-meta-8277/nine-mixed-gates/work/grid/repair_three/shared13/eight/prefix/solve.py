"""Normalize singleton line requirements and replay an exact line-prefix decision per class."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from functools import cache
from itertools import permutations
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "profiles"))
from line_prefix import encode, check_model
from profiles import SHAPES, permute
from run_first_mix import solve_and_replay
from sweep import digest


@cache
def bit_maps(width):
    return [tuple(1 << permute(code, order) for code in range(1 << width))
            for order in permutations(range(width))]


@cache
def row_maps(shape):
    types = SHAPES[shape]
    return [tuple(types.index(permute(kind, order)) for kind in types)
            for order in permutations(range(3))]


@cache
def images(width, codes):
    return tuple(sum(bits[c] for c in codes) for bits in bit_maps(width))


def normalize(case):
    s, w, gate_count = case["shape"], case["boundary"], case["line_gates"]
    codes = tuple(tuple(sorted(set(cs))) for cs in case["codes"])
    assert len(codes) == len(SHAPES[s]) and all(cs and min(cs) > 0 and max(cs) < 1 << w for cs in codes)
    # Lengths are invariant under boundary-wire renaming. Minimize the order of
    # lengths over row permutations before minimizing masks within that order.
    rows = row_maps(s)
    counts = [tuple(len(codes[i]) for i in row) for row in rows]
    low = min(counts)
    rows = [row for row, count in zip(rows, counts) if count == low]
    variants = [images(w, cs) for cs in codes]
    key = min(tuple(vals[i] for i in row) for vals in zip(*variants) for row in rows)
    assert len(set(c for cs in codes for c in cs)) == sum(map(len,codes))
    return s, w, gate_count, key


def prepare(inputs):
    groups = Counter()
    for path in inputs:
        data = json.loads(path.read_text())
        for item in data if isinstance(data,list) else data["remaining"]:
            groups[normalize(item)] += 1
    return [dict(shape=s,boundary=w,line_gates=g,
                 codes=[[i for i in range(1 << w) if bits >> i & 1] for bits in masks],
                 raw_profiles=count)
            for (s,w,g,masks),count in sorted(groups.items())]


def solve_one(item, directory, seconds):
    index, case = item
    folder = directory / f"{index:04d}"
    folder.mkdir()
    path = folder / "input.cnf"
    encoded = encode(path, case)
    verdict, _, lrat, actions = solve_and_replay(folder,seconds)
    result = dict(index=index,shape=case["shape"],boundary=case["boundary"],
                  line_gates=case["line_gates"],verdict=verdict,
                  sha256=digest(path),lrat=lrat,actions=actions)
    if verdict == "PROJECTED_SAT":
        result["line_masks"] = check_model(case, encoded, (folder / "solver.txt").read_text())
    return result


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("label")
    p.add_argument("inputs",type=Path,nargs="+")
    p.add_argument("--cache",type=Path,default=Path("cache"))
    p.add_argument("--seconds",type=int,default=30)
    p.add_argument("--jobs",type=int,default=4)
    a=p.parse_args()
    root=a.cache/f"L-meta-8277-eight-{a.label}"
    ledger=HERE/f"{a.label}-results.json"
    if root.exists() or ledger.exists():
        p.error("use a fresh label")
    groups=prepare(a.inputs)
    (HERE/f"{a.label}-classes.json").write_text(json.dumps(groups,separators=(',',':'))+'\n')
    print('Classes',Counter((g["shape"],g["boundary"],g["line_gates"]) for g in groups),flush=True)
    root.mkdir(parents=True)
    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        result=list(pool.map(lambda x: solve_one(x,root,a.seconds), enumerate(groups)))
    ledger.write_text(json.dumps(result,indent=2)+'\n')
    print('Results',Counter((r["shape"],r["verdict"]) for r in result),flush=True)
