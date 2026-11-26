"""Synthesize three line neighborhoods on singleton inputs using shared AND/OR gates."""

import argparse
import subprocess
import sys
from pathlib import Path

GRID = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(GRID.parent))
sys.path.insert(0, str(GRID / "search"))
from circuit_search import Encoder
from cases import BANK, ROWS


def subsets(mask):
    remaining = mask
    while remaining:
        yield remaining
        remaining = (remaining - 1) & mask


def project(triple, helpers):
    """Label lines by which of the three outputs must accept that singleton."""
    target_rows = [ROWS[index] for index in triple]

    def membership(line):
        return sum(((row >> line) & 1) << index for index, row in enumerate(target_rows))

    lines = sorted((i for i in range(11) if membership(i)), key=lambda i: (membership(i), i))

    def project_mask(mask):
        return sum(((mask >> line) & 1) << index for index, line in enumerate(lines))

    targets = tuple(project_mask(row) for row in target_rows)
    sources = [1 << i for i in range(11)] + BANK
    for index, row in enumerate(ROWS):
        if index in triple:
            continue
        if helpers == "balanced":
            a, b, c, d = [1 << i for i in range(11) if row >> i & 1]
            sources.extend((a | b, c | d, row))
        else:
            sources.extend(subsets(row))

    free = {project_mask(source) for source in sources}
    if helpers == "universal":
        universal = {
            mask for mask in range(1 << len(lines))
            if all((target & mask).bit_count() <= 1 for target in targets)
        }
        assert free <= universal
        free = universal

    assert all(t.bit_count() == 4 for t in targets)
    assert all((t & source).bit_count() <= 1 for source in free for t in targets)
    return sorted(free), targets, lines


def instance(path, free, targets, nlines, size):
    encoder = Encoder(path)
    one = encoder.var()
    encoder.clause(one)
    columns = [[one if mask >> i & 1 else -one for i in range(nlines)] for mask in free]

    def select(selectors, values):
        if all(abs(value) == one for value in values):
            output = encoder.var()
            for sign in [1, -1]:
                choices = [s for s, value in zip(selectors, values) if value == sign * one]
                encoder.clause(-sign * output, *choices)
            return output
        return encoder.mux(selectors, values)

    choices = []
    for _ in range(size):
        left, right = encoder.choose(len(columns)), encoder.choose(len(columns))
        for i in range(1, len(columns)):
            encoder.clause(-left[i], *right[i:])
        if choices:
            previous_right = choices[-1][1]
            for i in range(1, len(previous_right)):
                encoder.clause(-previous_right[i], *right[i:])

        is_and = encoder.var()
        choices.append((left, right, is_and))
        result = []
        for values in zip(*columns):
            a, b = select(left, values), select(right, values)
            out = encoder.var()
            result.append(out)
            encoder.clause(-is_and, -out, a)
            encoder.clause(-is_and, -out, b)
            encoder.clause(-is_and, -a, -b, out)
            encoder.clause(is_and, out, -a)
            encoder.clause(is_and, out, -b)
            encoder.clause(is_and, a, b, -out)
        columns.append(result)

    taps = []
    for target in targets:
        selectors = encoder.choose(size)
        for i, selector in enumerate(selectors):
            if i < 2:
                # The first two gates can combine at most three distinct leaf signals.
                encoder.clause(-selector)
                continue
            for line, value in enumerate(columns[len(free) + i]):
                encoder.clause(-selector, value if target >> line & 1 else -value)
        taps.append(selectors)

    # Trim dead gates, then pad a shorter circuit with copies of its last output.
    encoder.clause(*(tap[-1] for tap in taps))
    encoder.finish()
    return choices, taps


def verify_model(model, free, targets, choices, taps):
    def chosen(selectors):
        index, = [i for i, selector in enumerate(selectors) if selector in model]
        return index

    values = free.copy()
    for left, right, is_and in choices:
        a, b = chosen(left), chosen(right)
        print(len(values), "and" if is_and in model else "or", a, b)
        values.append(values[a] & values[b] if is_and in model else values[a] | values[b])
    outputs = [chosen(tap) for tap in taps]
    assert tuple(values[len(free) + index] for index in outputs) == targets
    print("output gates", outputs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("triple", choices=["".join(map(str, (a, b, c)))
                                          for a in range(6) for b in range(a + 1, 6)
                                          for c in range(b + 1, 6)])
    parser.add_argument("size", type=int)
    parser.add_argument("stem", type=Path)
    parser.add_argument("--seconds", type=int, default=90)
    parser.add_argument("--helpers", choices=["balanced", "subsets", "universal"], default="balanced")
    parser.add_argument("--proof", action="store_true")
    parser.add_argument("--solver", type=Path,
                        default=Path.home() / ".elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical")
    args = parser.parse_args()
    triple = tuple(map(int, args.triple))
    free, targets, lines = project(triple, args.helpers)
    path = args.stem.with_suffix(".cnf")
    choices, taps = instance(path, free, targets, len(lines), args.size)
    command = [args.solver, "-q", "-t", str(args.seconds)]
    if args.proof:
        command.extend(("--lrat", "--no-binary"))
    command.append(path)
    if args.proof:
        command.append(args.stem.with_suffix(".lrat"))
    print(f"{triple}, free={len(free)}, lines={lines}, targets={targets}, gates={args.size}", flush=True)
    result = subprocess.run(command, text=True, capture_output=True)
    print(next((line for line in result.stdout.splitlines() if line.startswith("s ")), "missing status"))
    if result.returncode == 10:
        model = {int(v) for line in result.stdout.splitlines() if line.startswith("v ")
                 for v in line[2:].split()}
        verify_model(model, free, targets, choices, taps)
    elif result.returncode != 20:
        raise SystemExit(f"Solver did not decide the instance: exit {result.returncode}, {result.stderr}")


if __name__ == "__main__":
    main()
