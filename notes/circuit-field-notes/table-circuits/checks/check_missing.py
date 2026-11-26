"""Replay explicit gates on every promised input and search the first small lower bound."""

from itertools import combinations


def input_tables(rows, cols):
    # Bit (r * cols + c) is the input activating row r and column c.
    rows_in = [sum(1 << (r * cols + c) for c in range(cols)) for r in range(rows)]
    cols_in = [sum(1 << (r * cols + c) for r in range(rows)) for c in range(cols)]
    return rows_in + cols_in


class Circuit:
    def __init__(self, rows, cols):
        self.inputs = input_tables(rows, cols)
        self.wires = self.inputs.copy()
        self.mask = (1 << (rows * cols)) - 1

    def gate(self, op, a, b=None):
        if op == "not":
            value = self.mask ^ self.wires[a]
        elif op == "or":
            value = self.wires[a] | self.wires[b]
        elif op == "and":
            value = self.wires[a] & self.wires[b]
        else:
            raise ValueError(op)
        self.wires.append(value)
        return len(self.wires) - 1

    def fold_or(self, wires):
        first, *rest = wires
        for other in rest:
            first = self.gate("or", first, other)
        return first

    def check_output(self, output, expected, cost):
        assert self.wires[output] == expected
        assert len(self.wires) - len(self.inputs) == cost


def check_constructions(rows, cols, s):
    matching = sum(1 << (i * cols + i) for i in range(s))
    circuit = Circuit(rows, cols)
    table = circuit.mask ^ matching
    pairs = [circuit.gate("and", i, rows + i) for i in range(s)]
    matched = circuit.fold_or(pairs)
    circuit.check_output(matched, matching, 2 * s - 1)
    signed = circuit.gate("not", matched)
    circuit.check_output(signed, table, 2 * s)

    if s == 3:
        positive = Circuit(rows, cols)
        x, y, z = [positive.gate("or", i, rows + i) for i in range(3)]
        xy_either = positive.gate("or", x, y)
        xy_both = positive.gate("and", x, y)
        majority = positive.gate("or", xy_both, positive.gate("and", z, xy_either))
        wild = positive.fold_or([*range(3, rows), *range(rows + 3, rows + cols)])
        result = positive.gate("or", majority, wild)
        positive.check_output(result, table, rows + cols + 1)
        repeated = sum(((64478 >> (4 * min(r, 3) + min(c, 3))) & 1) << (r * cols + c)
                       for r in range(rows) for c in range(cols))
        assert repeated == table


def reachable_signed(rows, cols, budget):
    # Constants are included for free. This makes an exclusion cover the project's
    # empty AND/OR gates as well. Equal tables can share a wire on every later gate.
    mask = (1 << (rows * cols)) - 1
    initial = frozenset([0, mask, *input_tables(rows, cols)])
    states = {initial}
    reachable = set(initial)
    for step in range(budget):
        next_states = set()
        for state in states:
            candidates = {mask ^ a for a in state}
            for a, b in combinations(state, 2):
                candidates.update((a & b, a | b))
            candidates -= state
            reachable.update(candidates)
            if step + 1 < budget:
                next_states.update(state | {value} for value in candidates)
        states = next_states
    return reachable


def minimum_observed_support(rows, cols, s):
    # Group all promised inputs by their visible wire values for each candidate support.
    cells = [(r, c, (1 << r) | (1 << (rows + c))) for r in range(rows) for c in range(cols)]
    for size in range(rows + cols + 1):
        for ids in combinations(range(rows + cols), size):
            keep = sum(1 << i for i in ids)
            yes = {bits & keep for r, c, bits in cells if r != c or r >= s}
            no = {bits & keep for r, c, bits in cells if r == c and r < s}
            if yes.isdisjoint(no):
                return size
    raise AssertionError("The full input always determines the table")


if __name__ == "__main__":
    checks = 0
    for rows in range(3, 10):
        for cols in range(3, 10):
            for s in range(2, min(rows, cols)):
                check_constructions(rows, cols, s)
                checks += 1
    print(f"Gate lists and truth tables agree on {checks} rectangular matching instances.")
    target = ((1 << 9) - 1) ^ (1 | (1 << 4))
    assert target not in reachable_signed(3, 3, 3)
    print("Exhaustive 3×3 search excludes every signed circuit through three gates for two holes.")
    for rows, cols, s in [(3, 3, 2), (4, 4, 3), (5, 6, 3), (5, 5, 4)]:
        assert minimum_observed_support(rows, cols, s) == 2 * s
    print("Four direct input-support enumerations attain 2s, including six for mask 64478.")
