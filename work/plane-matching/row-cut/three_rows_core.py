"""Exact synthesis on the six incidences left after the second restriction."""
import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from circuit_search import Encoder

# Bit positions here name lines. Row order names the first three point inputs.
TARGET = {"common": (3, 5, 9), "triangle": (3, 5, 6)}


def samples(rows):
    width = max(rows).bit_length()
    positives = [(1 << r, 1 << j, True) for r, row in enumerate(rows)
                 for j in range(width) if row >> j & 1]
    negatives = [(p, m) for p in range(8) for m in range(1 << width)
                 if p.bit_count() <= 2 and m.bit_count() <= 2
                 and all(not (p >> i & 1 and m & row) for i, row in enumerate(rows))]
    # Monotonicity permits keeping only the maximal members of this finite set.
    maxima = [(p, m, False) for p, m in negatives if not any(
        (q, n) != (p, m) and p & q == p and m & n == m for q, n in negatives)]
    return positives + maxima


def encode(path, shape, size):
    rows = TARGET[shape]
    width = max(rows).bit_length()
    tests = samples(rows)
    enc = Encoder(path)
    one = enc.var()
    enc.clause(one)
    signals = [[one if (p | m << 3) >> i & 1 else -one for p,m,_ in tests]
               for i in range(3 + width)]
    previous = None
    wiring = []
    for _ in range(size):
        left = enc.choose(len(signals))
        right = enc.choose(len(signals))
        for j in range(1, len(left)):
            enc.clause(-left[j], *right[j:])
        if previous is not None:
            for j in range(1, len(previous)):
                enc.clause(-previous[j], *right[j:])
        previous = right
        is_and = enc.var()
        wiring.append((left, right, is_and))
        outputs = []
        for values in zip(*signals):
            a = enc.mux(left, values)
            b = enc.mux(right, values)
            y = enc.var()
            enc.clause(-is_and, -y, a)
            enc.clause(-is_and, -y, b)
            enc.clause(-is_and, -a, -b, y)
            enc.clause(is_and, y, -a)
            enc.clause(is_and, y, -b)
            enc.clause(is_and, -y, a, b)
            outputs.append(y)
        signals.append(outputs)
    for y, (_, _, positive) in zip(signals[-1], tests):
        enc.clause(y if positive else -y)
    enc.finish()
    return wiring


if __name__ == "__main__":
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("shape", choices=TARGET)
    args.add_argument("size", type=int)
    args.add_argument("output", type=Path)
    options = args.parse_args()
    encode(options.output, options.shape, options.size)
