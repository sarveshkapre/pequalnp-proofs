"""Rebuild exact-eight line problems, verify every proof, and decode a passing planted control per problem."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path

from solve import HERE, prepare
from check import check_one


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("label")
    p.add_argument("inputs",type=Path,nargs="+")
    p.add_argument("--cache",type=Path,default=Path("cache"))
    p.add_argument("--jobs",type=int,default=4)
    a = p.parse_args()
    classes = json.loads((HERE/f"{a.label}-classes.json").read_text())
    result = json.loads((HERE/f"{a.label}-results.json").read_text())
    assert classes == prepare(a.inputs), "extracted classes differ from saved ledger"
    assert len(result) == len(classes) and len(result) > 0
    root = a.cache/f"L-meta-8277-eight-{a.label}"
    def check_index(i):
        record,case = result[i],classes[i]
        assert record["index"] == i
        assert all(case[k] == record[k] for k in ("shape","boundary","line_gates"))
        check_one(case,record,f"{i:04d}",root)
    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        list(pool.map(check_index,range(len(classes))))
    print(a.label, len(result), "regenerated formulas, matching proof hashes, successful LRAT replays and planted controls.")
    print("Shapes:",dict(Counter(r["shape"] for r in result)))
