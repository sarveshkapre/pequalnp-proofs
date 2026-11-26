"""Replay the two gate lists against the boundary tests in R_meta_4893_629."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ROWS = (29, 225, 1793, 294, 586, 1170)
PORTS = (3, 40, 1064, 272, 336, 516, 644, 48, 560, 264, 392, 68, 1092)


def read_gates(name):
    gates = []
    for line in (ROOT / name).read_text().splitlines():
        op, left, right = line.split()
        a, b = int(left), int(right)
        if op not in {"and", "or"} or not 0 <= min(a, b) <= max(a, b) < 30 + len(gates):
            raise ValueError(f"Invalid gate on wire {30 + len(gates)}: {line}")
        gates.append((op, a, b))
    return gates


def trace(gates, p, w, clamp=None):
    wires = [bool(p & (1 << i)) for i in range(6)]
    wires.extend(bool(w & (1 << j)) for j in range(11))
    wires.extend(bool(w & mask) for mask in PORTS)
    for index, (op, a, b) in enumerate(gates, start=30):
        value = wires[a] and wires[b] if op == "and" else wires[a] or wires[b]
        wires.append(value and index != clamp)
    return wires


def maximal_negatives():
    masks = set()
    for w in range(1 << 11):
        if any((w & group).bit_count() > 2 for group in ROWS + PORTS):
            continue
        for p in range(1 << 6):
            if p & 7 == 7 or p & 56 == 56:
                continue
            if all(not (p & (1 << i) and w & row) for i, row in enumerate(ROWS)):
                masks.add(p | (w << 6))
    return sorted((x & 63, x >> 6) for x in masks
                  if all(x | (1 << i) not in masks for i in range(17) if not x & (1 << i)))


def main():
    positives = [(i, j) for i, row in enumerate(ROWS) for j in range(11) if row & (1 << j)]
    negatives = maximal_negatives()
    if (len(positives), len(negatives)) != (24, 153):
        raise ValueError("The grid tests do not match the published counts")
    for size, name, expected in [(28, "grid28.txt", [(2, 9), (2, 10), (3, 5)]),
                                 (29, "grid29.txt", [])]:
        gates = read_gates(name)
        missed = [(i, j) for i, j in positives if not trace(gates, 1 << i, 1 << j)[-1]]
        accepted = [(p, w) for p, w in negatives if trace(gates, p, w)[-1]]
        print(f"{name}: {len(gates)} gates, missed positives {missed}, "
              f"accepted {len(accepted)}/{len(negatives)} maximal negatives")
        if (len(gates), missed, accepted) != (size, expected, []):
            raise ValueError(f"Unexpected result in {name}")
    gates = read_gates("grid28.txt")
    negative = trace(gates, 8, 1)
    ordinary = trace(gates, 4, 1)[-1]
    clamped = trace(gates, 4, 1, clamp=43)[-1]
    if (negative[43], negative[50], negative[-1], ordinary, clamped) != (True, False, False, True, False):
        raise ValueError("Unexpected trace")
    print("On (point 3, line 0), wire 43 = 1, wire 50 = 0, output = 0.")
    print("On (point 2, line 0), forcing wire 43 to 0 changes the output from 1 to 0.")


if __name__ == "__main__":
    main()
