"""Independent CNF encoding of four exceptional gates on a-b-c plus d-e.

Vertices occupy bits 0,...,4. Literals in the encoder are signed DIMACS
integers; variable 1 is fixed true. A gate has one physical choice of operands
for every tested input. Use order OAAOO for the larger passing control.
"""
import argparse
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path


class CNF:
    def __init__(self):
        self.last = 1
        self.clauses = [[1]]

    def bit(self):
        self.last += 1
        return self.last

    def clause(self, *lits):
        items = dict.fromkeys(lits)
        if 1 in items or any(-v in items for v in items):
            return
        self.clauses.append([v for v in items if v != -1])

    def disj(self, lits):
        items = list(dict.fromkeys(x for x in lits if x != -1))
        if 1 in items or any(-x in items for x in items):
            return 1
        if not items:
            return -1
        if len(items) == 1:
            return items[0]
        out = self.bit()
        self.clause(-out, *items)
        for item in items:
            self.clause(-item, out)
        return out

    def conj(self, lits):
        return -self.disj(-x for x in lits)

    def choose(self, options):
        result = {o: self.bit() for o in options}
        self.clause(*result.values())
        for a, b in combinations(result.values(), 2):
            self.clause(-a, -b)
        return result

    def constant(self, truth):
        return 1 if truth else -1

    def dimacs(self):
        return f"p cnf {self.last} {len(self.clauses)}\n" + "".join(
            " ".join(map(str, (*clause, 0))) + "\n" for clause in self.clauses)


@dataclass
class Wire:
    raw: list
    present: int
    values: list


BASE = (0, 1, 2, 4, 8, 16, 9, 12, 18)
EDGES = (3, 6, 24)


class Model:
    def __init__(self, order, mode):
        self.cnf = f = CNF()
        self.mode = mode
        edges = EDGES + ((20,) if mode == "cross" else ())
        self.rows = list(range(32))
        self.negative = [x for x in self.rows if all(x & e != e for e in edges)]
        self.gates = []
        self.ors = []
        for op in order:
            u, v = self.port(), self.port()
            if op == "O":
                out = Wire([f.disj(pair) for pair in zip(u.raw, v.raw)],
                           f.disj([u.present, v.present]),
                           [f.disj(pair) for pair in zip(u.values, v.values)])
                self.ors.append(out)
            else:
                out = Wire([-1] * 5, -1, [f.conj(pair) for pair in zip(u.values, v.values)])
            self.gates.append(out)

        # At most one outside centre per selected OR, and arbitrarily many
        # outside tops with empty centre contributions can be dropped.
        center_sets = []
        outputs = []
        for _ in self.ors:
            csel, center = self.top_port((0,))
            center_sets.append(csel)
            lsel, leaf = self.top_port(BASE)
            for c, l in zip(csel, lsel):
                f.clause(-c, -l)
            safe = f.bit()
            for r in self.negative:
                f.clause(-safe, -center.values[r])
                f.clause(-center.values[r], -leaf.values[r])
                if mode != "outside" and not r & 4:
                    f.clause(-center.values[r])
            if mode == "outside":
                # A negative centre valuation forces its matched leaf to be c.
                f.clause(safe, leaf.raw[2])
            outputs.append([f.conj([c, f.disj([safe, l])])
                            for c, l in zip(center.values, leaf.values)])
        if mode != "outside":
            csel, center = self.top_port((4,))
            center_sets.append(csel)
            lsel, leaf = self.top_port((0, 16) if mode == "cross" else (0,))
            for c, l in zip(csel, lsel):
                f.clause(-c, -l)
            output = [f.conj(pair) for pair in zip(center.values, leaf.values)]
            for r in self.negative:
                f.clause(-output[r])
            outputs.append(output)
        for x, y in combinations(center_sets, 2):
            for p, q in zip(x, y):
                f.clause(-p, -q)
        # Only the three residual positives are required, including in cross.
        for r in EDGES:
            f.clause(*(out[r] for out in outputs))

    def top_port(self, masks):
        f = self.cnf
        choose = f.choose(masks)
        base = [f.disj(v for mask, v in choose.items() if mask & (1 << i)) for i in range(5)]
        selected = [f.bit() for _ in self.ors]
        for sel, wire in zip(selected, self.ors):
            f.clause(-sel, wire.present)
            for b, support in zip(base, wire.raw):
                f.clause(-sel, -support, b)
        values = []
        for r in self.rows:
            terms = [v for m, v in choose.items() if r & m]
            terms.extend(f.conj([sel, w.values[r]]) for sel, w in zip(selected, self.ors))
            values.append(f.disj(terms))
        return selected, Wire(base, 1, values)

    def port(self):
        f = self.cnf
        _, ordinary = self.top_port(BASE)
        choices = [ordinary, *self.gates]
        selectors = f.choose(range(len(choices)))

        def mux(values):
            return f.disj(f.conj([selectors[i], value]) for i, value in enumerate(values))
        return Wire([mux(w.raw[j] for w in choices) for j in range(5)],
                    mux(w.present for w in choices),
                    [mux(w.values[r] for w in choices) for r in self.rows])


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("mode", choices=("outside", "inside", "cross"))
    p.add_argument("order", help="Gate order, e.g. AOAO")
    p.add_argument("output", type=Path)
    args = p.parse_args()
    if set(args.order) - {"A", "O"}:
        p.error("expected A and O")
    args.output.write_text(Model(args.order, args.mode).cnf.dimacs())
