"""Verify each distinct residual formula by direct unit propagation on its LRAT hints."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def read_formula(data):
    header, *rows = data.decode().splitlines()
    prefix, kind, variables, count = header.split()
    assert (prefix, kind) == ("p", "cnf") and len(rows) == int(count)
    clauses = {}
    for index, row in enumerate(rows, 1):
        literals = list(map(int, row.split()))
        assert literals[-1] == 0 and all(0 < abs(v) <= int(variables) for v in literals[:-1])
        clauses[index] = frozenset(literals[:-1])
    return clauses


def proves_clause(clause, hints, clauses):
    # Negate the proposed clause. Every hint must force a value or yield a conflict.
    true = {-literal for literal in clause}
    if any(-v in true for v in true):
        return True
    for index in hints:
        assert index > 0  # These certificates use only unit-propagation hints.
        premise = clauses[index]
        assert true.isdisjoint(premise)
        unassigned = [literal for literal in premise if -literal not in true]
        if not unassigned:
            return True
        assert len(unassigned) == 1
        true.add(unassigned[0])
    return False


def verify(problem, proof):
    clauses = read_formula(problem)
    for row in proof.decode().splitlines():
        words = row.split()
        assert words[-1] == "0"
        if words[1] == "d":
            for index in words[2:-1]:
                del clauses[int(index)]
            continue
        separator = words.index("0", 1)
        clause = frozenset(map(int, words[1:separator]))
        hints = list(map(int, words[separator + 1:-1]))
        assert int(words[0]) not in clauses
        assert proves_clause(clause, hints, clauses)
        if not clause:
            return
        clauses[int(words[0])] = clause
    raise AssertionError("proof ended before it derived a contradiction")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache", type=Path, default=Path("cache"))
    opts = parser.parse_args()
    checked = set()
    entries = 0
    for label in ("tree", "fan-verify"):
        ledger = json.loads((HERE / "prefix" / f"{label}-results.json").read_text())
        for record in ledger:
            folder = opts.cache / f"L-meta-8277-eight-{label}" / f"{record['index']:04d}"
            problem = (folder / "input.cnf").read_bytes()
            proof = (folder / "proof.lrat").read_bytes()
            digest = hashlib.sha256(problem).hexdigest()
            assert digest == record["sha256"] and hashlib.sha256(proof).hexdigest() == record["lrat"]
            entries += 1
            if digest not in checked:
                verify(problem, proof)
                checked.add(digest)
    print(f"{entries} entries, {len(checked)} distinct formulas. Each derived the empty clause.")
