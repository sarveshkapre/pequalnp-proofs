import sys
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "search"))
from cases import ROWS, bank, cases

def lines(row):
    return [i for i in range(11) if ROWS[row] & (1 << i)]

def traces(gates, samples):
    ports = [bank(p, w) for p, w, _ in samples]
    values = [sum(((v >> wire) & 1) << k for k, v in enumerate(ports))
              for wire in range(30)]
    for op, a, b in gates:
        assert 0 <= a < len(values) and 0 <= b < len(values)
        assert op in ("and", "or")
        values.append(values[a] & values[b] if op == "and" else values[a] | values[b])
    return values

def layout(active, omit=None):
    fixed, joint = [], []
    def gate(seq, op, a, b):
        wire = 30 + len(fixed) + len(joint)
        seq.append((op, a, b))
        return wire
    def branch(seq, row):
        ports = [6 + i for i in lines(row) if (row, i) != omit]
        v = ports[0]
        for w in ports[1:]:
            v = gate(seq, "or", v, w)
        return gate(seq, "and", v, row)
    frozen = [branch(fixed, row) for row in range(6) if row not in active]
    terms = [branch(joint, row) for row in active]
    v = gate(joint, "or", terms[0], terms[1])
    v = gate(joint, "or", v, terms[2])
    suffix = []
    for w in frozen:
        suffix.append(("or", v, w))
        v = 29 + len(fixed) + len(joint) + len(suffix)
    return fixed, joint, suffix
