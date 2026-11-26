"""Enumerate the projected path circuits. Uses only the Python standard library."""

from dataclasses import dataclass
from itertools import combinations


@dataclass(frozen=True, order=True)
class Wire:
    values: int      # One bit per assignment on the four path vertices.
    raw: int         # Path vertices reachable through ORs alone.
    nonempty: bool   # Includes raw vertices outside the path.


LITERALS = tuple(
    sum(1 << row for row in range(16) if row & (1 << vertex))
    for vertex in range(4)
)
TARGET = (LITERALS[0] & LITERALS[1]) | (LITERALS[1] & LITERALS[2]) | (LITERALS[2] & LITERALS[3])
BASES = (Wire(0, 0, True),) + tuple(Wire(value, 1 << i, True) for i, value in enumerate(LITERALS))


def combine(op, left, right):
    if op == 'AND':
        return Wire(left.values & right.values, 0, False)
    assert op == 'OR'
    return Wire(left.values | right.values, left.raw | right.raw, left.nonempty or right.nonempty)


def ports(gates):
    ordinary = set(BASES)
    for op, wire in gates:
        if op == 'OR' and wire.nonempty:
            merged = {combine('OR', base, wire) for base in ordinary}
            ordinary.update(w for w in merged if w.raw.bit_count() <= 1)
    return sorted(ordinary | {wire for _, wire in gates})


def covers(gates):
    covered = 0
    for op, wire in gates:
        if op == 'OR' and wire.nonempty and wire.raw == 0 and wire.values & ~TARGET == 0:
            covered |= wire.values
    return covered == TARGET


def search(order):
    def visit(gates):
        if covers(gates):
            return gates
        if len(gates) == len(order):
            return None
        op = order[len(gates)]
        choices = ports(gates)
        outputs = {
            combine(op, left, right)
            for i, left in enumerate(choices)
            for right in choices[i:]
        }
        for wire in sorted(outputs):
            witness = visit(gates + ((op, wire),))
            if witness is not None:
                return witness
        return None

    return visit(())


def check_control():
    # A third OR suffices in the model: build b(a+c)+cd, then read the result
    # through a nonempty raw input outside the path (zero in all 16 rows).
    outside, a, b, c, d = BASES
    gates = []

    def add(op, left, right):
        available = ports(gates)
        assert left in available and right in available
        output = combine(op, left, right)
        gates.append((op, output))
        return output

    a_or_c = add('OR', a, c)
    first = add('AND', a_or_c, b)
    last = add('AND', c, d)
    path = add('OR', first, last)
    assert path.values == TARGET and not path.nonempty and not covers(gates)
    add('OR', path, outside)
    assert covers(gates)


if __name__ == '__main__':
    check_control()
    print('Positive control: two ANDs and three ORs cover the path.')
    for positions in combinations(range(4), 2):
        order = tuple('AND' if i in positions else 'OR' for i in range(4))
        witness = search(order)
        print(' '.join(order), 'no circuit' if witness is None else witness, flush=True)
        assert witness is None
