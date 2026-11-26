"""Verify the vertex-critical tree and exhaust the formula and circuit lower bounds."""
import argparse
from functools import cache
from itertools import product
import json
from pathlib import Path
import subprocess

RECT = ("R", ())
HERE = Path(__file__).resolve().parent


def check(condition, message):
    if not condition:
        raise ValueError(message)


def node(op, left, right):
    children = []
    for child in (left, right):
        children.extend(child[1] if child[0] == op else [child])
    return op, tuple(sorted(children))


@cache
def shapes(cost):
    if cost == 0:
        return {RECT}
    result = set()
    for left in range(cost):
        for a, b in product(shapes(left), shapes(cost - 1 - left)):
            result.add(node("U", a, b))
    for left in range(1, cost):
        for a, b in product(shapes(left), shapes(cost - left)):
            result.add(node("I", a, b))
    return result


def leaf_count(shape):
    return 1 if shape == RECT else sum(map(leaf_count, shape[1]))


def zero_table(shape):
    def evaluate(tree, bits):
        if tree == RECT:
            return next(bits)
        # Consume all children before applying all/any so leaf positions are fixed.
        values = [evaluate(child, bits) for child in tree[1]]
        return all(values) if tree[0] == "I" else any(values)
    width = leaf_count(shape)
    return tuple(evaluate(shape, iter(bool(x & (1 << b)) for b in range(width)))
                 for x in range(1 << width))


def circuit_edge(word, wiring, output):
    # Bit b is true exactly where free star-union b has value zero.
    gates = 0
    for i, (left, right) in enumerate(wiring):
        a = not (word & (1 << (2*i))) or bool(gates & left)
        b = not (word & (1 << (2*i + 1))) or bool(gates & right)
        if a and b:
            gates |= 1 << i
    return bool(gates & output)


def evaluate_labels(certificate, width, edge):
    rows = certificate["row_words"]
    cols = certificate["column_words"]
    check(all(0 <= x < 1 << width for x in rows + cols), "label outside alphabet")
    return [[bool(edge(x & y)) for y in cols] for x in rows]


def get_tree(data):
    neighbors = data["neighbors"]
    check(len(neighbors) == 10, "row count")
    graph = [set() for _ in range(20)]
    for i, row in enumerate(neighbors):
        check(len(row) == len(set(row)) and all(0 <= j < 10 for j in row), "bad edge")
        for j in row:
            graph[i].add(10+j)
            graph[10+j].add(i)
    seen, todo = {0}, [0]
    while todo:
        for v in graph[todo.pop()] - seen:
            seen.add(v)
            todo.append(v)
    check(len(seen) == 20 and sum(map(len, neighbors)) == 19, "tree check failed")
    return [[j in row for j in range(10)] for row in neighbors]


def witness_checks(data, formulas):
    target = get_tree(data)
    wiring = [(0, 0), (0, 1), (0, 3), (1, 2)]
    circuit = evaluate_labels(data["circuit"], 8, lambda x: circuit_edge(x, wiring, 12))
    flat = evaluate_labels(data["flat_formula"], 6, lambda x: x == 0)
    check(circuit == flat == target, "construction mismatch")
    checked = set()
    for item in data["deletions"]:
        side, vertex = item["shore"], item["vertex"]
        check(side in ("row", "column") and 0 <= vertex < 10, "bad deletion")
        reduced = [[value for j, value in enumerate(row) if (side, vertex) != ("column", j)]
                   for i, row in enumerate(target) if (side, vertex) != ("row", i)]
        shape = formulas[item["shape"]]
        table = zero_table(shape)
        actual = evaluate_labels(item, leaf_count(shape), lambda x: not table[x])
        check(actual == reduced, "deletion mismatch")
        checked.add((side, vertex))
    check(len(checked) == len(data["deletions"]) == 20, "missing or repeated deletion")
    return target


def host_profiles(zeros):
    # Equal full rows are interchangeable. Symmetry gives the same column types.
    types = {}
    for x in range(len(zeros)):
        neighbors = tuple(not zeros[x & y] for y in range(len(zeros)))
        if any(neighbors) and not all(neighbors):
            types.setdefault(neighbors, x)
    words = list(types.values())
    return ["".join("0" if zeros[x & y] else "1" for y in reversed(words)) for x in words]


def three_gate_tables():
    # Ordered arms are kept, as are unused gates and all output subsets.
    for a, b, c, d, taps in product(range(2), range(2), range(4), range(4), range(8)):
        wiring = [(0, 0), (a, b), (c, d)]
        yield tuple(not circuit_edge(x, wiring, taps) for x in range(64))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checker", type=Path)
    args = parser.parse_args()
    formulas = sorted(shapes(4))
    check(len(formulas) == 9, "normal forms")
    target = witness_checks(json.loads((HERE / "witness.json").read_text()), formulas)
    print("Tree: 20 vertices, 19 edges. Circuit and formula: 100/100 cells each.")
    print("Every one of 20 vertex deletions has a four-intersection formula (1800 cells).")
    jobs, answers, labels = [], [], []

    def schedule(matrix, host, answer, label):
        rows, cols = len(matrix), len(matrix[0])
        for side in (matrix, list(zip(*matrix))):
            check(all(any(s) and not all(s) for s in side), "constant target profile")
            check(len({tuple(s) for s in side}) == len(side), "duplicate target profile")
        if len(host) < max(rows, cols):
            check(not answer, "too few host types for positive control")
            return
        masks = [sum(1 << j for j, value in enumerate(row) if value) for row in matrix]
        jobs.append(" ".join(map(str, [len(jobs), rows, cols, len(host), *masks, *host])))
        answers.append(int(answer))
        labels.append(label)

    matching = [[i == j for j in range(4)] for i in range(4)]
    for i, shape in enumerate(formulas):
        host = host_profiles(zero_table(shape))
        schedule(target, host, False, f"formula {i}")
        schedule(matching, host, True, f"positive control {i}")
    tables = list(three_gate_tables())
    check(len(tables) == 512, "circuit enumeration")
    for table in sorted(set(tables)):
        schedule(target, host_profiles(table), False, "three-gate circuit")
    run = subprocess.run([str(args.checker.resolve())], input="\n".join(jobs) + "\n",
                         capture_output=True, text=True, check=True)
    records = [list(map(int, line.split())) for line in run.stdout.splitlines()]
    check(len(records) == len(jobs), "incomplete checker output")
    for i, (tag, fit, visits) in enumerate(records):
        check(tag == i and fit == answers[i] and visits > 0, f"failed at {labels[i]}")
        if labels[i].startswith("formula"):
            print(f"{labels[i]} excluded ({visits:,} search nodes)")
    print("All 9 four-gate formulas excluded; all 9 positive controls represented.")
    print(f"All 512 ordered three-gate wirings/output choices excluded ({len(set(tables))} scalar tables).")
    print("Exact intersection costs: circuit 4, formula 5.")


if __name__ == "__main__":
    main()
