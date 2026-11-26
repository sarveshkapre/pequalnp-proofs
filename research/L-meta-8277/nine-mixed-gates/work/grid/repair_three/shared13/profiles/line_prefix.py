"""Find line circuits supplying the allowed boundary codes of a mixed suffix."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations
import json
from pathlib import Path

from profiles import SHAPES
from line_order import canonicalize
from run_first_mix import solve_and_replay
from split import Encoder, project
from sweep import digest


def encode(path, case, boundary_rules=None):
    shape, width, size = case["shape"], case["boundary"], case["line_gates"]
    free, targets, lines = project(tuple(map(int, shape)), "universal")
    allowed = []
    if boundary_rules is None:
        by_type = dict(zip(SHAPES[shape], case["codes"], strict=True))
        allowed = [by_type[sum(((row >> j) & 1) << i for i, row in enumerate(targets))]
                   for j in range(len(lines))]
    enc = Encoder(path)
    conflicts = {edge for row in targets for edge in combinations(
        [i for i in range(len(lines)) if row >> i & 1], 2)}
    columns, specs = [], []

    def operand():
        selectors = enc.choose(1 + len(columns))
        mask = [enc.var() for _ in lines]
        for bit in mask:
            enc.clause(-bit, selectors[0])
        for a, b in sorted(conflicts):
            enc.clause(-mask[a], -mask[b])
        result = []
        for j in range(len(lines)):
            value = enc.var()
            enc.clause(-selectors[0], -value, mask[j])
            enc.clause(-mask[j], value)
            for selector, column in zip(selectors[1:], columns, strict=True):
                enc.clause(-selector, -value, column[j])
                enc.clause(-selector, value, -column[j])
            result.append(value)
        return (selectors, mask), result

    previous = []
    for _ in range(size):
        left, a = operand()
        right, b = operand()
        op = enc.var()
        specs.append((left, right, op))
        for idx in range(1, len(left[0])):
            enc.clause(-left[0][idx], *right[0][idx:])
        for idx in range(1, len(previous)):
            enc.clause(-previous[idx], *right[0][idx:])
        previous = right[0]
        col = []
        for u, v in zip(a, b):
            z = enc.var()
            enc.clause(-op, -z, u)
            enc.clause(-op, -z, v)
            enc.clause(-op, z, -u, -v)
            enc.clause(op, z, -u)
            enc.clause(op, z, -v)
            enc.clause(op, -z, u, v)
            col.append(z)
        columns.append(col)
    canonicalize(enc, specs, targets, len(lines))
    taps = []
    selected = []
    for i in range(width):
        side, col = operand()
        taps.append(side)
        selected.append(col)
        mandatory = sum(1 << j for j, codes in enumerate(allowed) if all(c >> i & 1 for c in codes))
        # A circuit of k gates has at most k+1 different leaves in its output cone.
        needed = max((mandatory & row).bit_count() - 1 for row in targets)
        for selector in side[0][:max(0, needed)]:
            enc.clause(-selector)
    for j, codes in enumerate(allowed):
        for forbidden in set(range(1 << width)) - set(codes):
            enc.clause(*[-col[j] if forbidden >> i & 1 else col[j] for i, col in enumerate(selected)])
    if boundary_rules is not None:
        boundary_rules(enc, selected, targets)
    enc.finish()
    return specs, taps, free, allowed


def check_model(case, encoded, solver_text):
    specs, taps, free, allowed = encoded
    model = {int(t) for line in solver_text.splitlines() if line.startswith("v ") for t in line[2:].split()}
    wires = []
    def wire(side):
        selectors, bits = side
        idx, = [i for i, v in enumerate(selectors) if v in model]
        if idx:
            return wires[idx - 1]
        mask = sum((v in model) << i for i, v in enumerate(bits))
        assert mask in free
        return mask
    for left, right, op in specs:
        a, b = wire(left), wire(right)
        wires.append(a & b if op in model else a | b)
    masks = [wire(tap) for tap in taps]
    assert all(sum(((mask >> j) & 1) << i for i, mask in enumerate(masks)) in codes
               for j, codes in enumerate(allowed))
    return masks


def run(item, root, seconds):
    idx, case = item
    out = root / str(idx)
    out.mkdir()
    cnf = out / "input.cnf"
    encoded = encode(cnf, case)
    verdict, _, lrat, actions = solve_and_replay(out, seconds)
    result = dict(index=idx, shape=case["shape"], total=case["total"], verdict=verdict,
                  sha256=digest(cnf), lrat=lrat, actions=actions)
    if verdict == "PROJECTED_SAT":
        result["line_masks"] = check_model(case, encoded, (out / "solver.txt").read_text())
    print(idx, case["shape"], verdict, actions, flush=True)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profiles", type=Path)
    parser.add_argument("cache", type=Path)
    parser.add_argument("ledger", type=Path)
    parser.add_argument("--seconds", type=int, default=45)
    parser.add_argument("--jobs", type=int, default=3)
    args = parser.parse_args()
    if args.cache.exists() or args.ledger.exists():
        parser.error("use a fresh cache directory and ledger")
    args.cache.mkdir(parents=True)
    cases = json.loads(args.profiles.read_text())["remaining"]
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda item: run(item, args.cache, args.seconds), enumerate(cases)))
    args.ledger.write_text(json.dumps(results, indent=2) + "\n")
