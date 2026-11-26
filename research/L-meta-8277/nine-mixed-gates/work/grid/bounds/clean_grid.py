from itertools import combinations
from pathlib import Path
import argparse
import ast
import re

ROWS = (29, 225, 1793, 294, 586, 1170)
PORTS = (3, 40, 1064, 272, 336, 516, 644, 48, 560, 264, 392, 68, 1092)
NEGATIVE_COVER = (
    (0, 1091), (2, 534), (2, 1290), (5, 162), (9, 1728), (12, 216), (16, 389),
    (16, 1073), (18, 1300), (30, 16), (33, 864), (36, 108), (40, 521), (51, 256),
)


def bits(mask):
    return [i for i in range(mask.bit_length()) if mask >> i & 1]

def row_stars(omit=None):
    gates = []

    def add(op, a, b):
        gates.append((op, a, b))
        return 29 + len(gates)

    def join(ids):
        head, *tail = ids
        for wire in tail:
            head = add("or", head, wire)
        return head

    terms = []
    for i, row in enumerate(ROWS):
        operands = [6 + j for j in bits(row) if (i, j) != omit]
        terms.append(add("and", i, join(operands)))
    return gates, join(terms)
