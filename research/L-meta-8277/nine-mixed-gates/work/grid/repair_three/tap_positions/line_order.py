"""Break symmetries of interchangeable singleton lines and pairs of raw line operands."""
from collections import defaultdict


def lex_ge(enc, left, right, guards=()):
    """Require left >= right lexicographically when all guards hold."""
    if len(left) != len(right):
        raise ValueError("Lexicographic comparisons require equal lengths")
    active = [-g for g in guards]
    for i, (x, y) in enumerate(zip(left, right)):
        enc.clause(*active, x, -y)
        if i == len(left) - 1:
            break
        equal_so_far = enc.var()
        # If the previous prefix and this bit agree, the next comparison is active.
        # Otherwise the auxiliary may be false.
        enc.clause(*active, x, y, equal_so_far)
        enc.clause(*active, -x, -y, equal_so_far)
        active = [-equal_so_far]


def canonicalize(enc, gate_specs, targets, nlines):
    masks = [side[1] for left, right, _ in gate_specs for side in (left, right)]
    classes = defaultdict(list)
    for col in range(nlines):
        classes[tuple((t >> col) & 1 for t in targets)].append(col)
    for cols in classes.values():
        for a, b in zip(cols, cols[1:]):
            lex_ge(enc, [m[a] for m in masks], [m[b] for m in masks])
    for left, right, _ in gate_specs:
        lex_ge(enc, left[1], right[1], guards=(left[0][0], right[0][0]))


def canonicalize_envelope(enc, gate_specs, targets, nlines):
    """Keep the largest mask-bit matrix under permutations preserving the whole bank."""
    from physical_masks import forbidden_exact, stabilizer
    masks = [side[1] for left, right, _ in gate_specs for side in (left, right)]
    excluded = set(forbidden_exact(targets))
    bank = {s for s in range(1 << nlines)
            if s not in excluded and all((s & target).bit_count() <= 1 for target in targets)}
    for perm in stabilizer(bank, targets):
        moved = [i for i, j in enumerate(perm) if i != j]
        if moved:
            left = [row[i] for row in masks for i in moved]
            right = [row[perm[i]] for row in masks for i in moved]
            lex_ge(enc, left, right)
    for left, right, _ in gate_specs:
        lex_ge(enc, left[1], right[1], guards=(left[0][0], right[0][0]))
