"""Classify projected grid input banks up to permutations preserving all three row roles.

A physical bank grants every line-subset OR of the frozen rows. This relaxation
covers all ways of associating their ORs. Each envelope below contains a relabeling
of every such bank of its shape. The envelope sizes are feasible, not claimed optimal.
"""

from collections import Counter, defaultdict
from functools import cache
from itertools import permutations, product
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "line"))
from triple_line import project


# Canonical numbering is that of project(): sort by the three-bit row-membership
# signature, then by physical line number. After a relabeling, each role keeps
# exactly the same set of incidences, although the ambient physical lines may move.
EXCLUDED = {
    (519, 568, 960): (20, 34, 66, 73, 76, 80, 82, 84, 97, 98, 138, 140,
                      145, 146, 161, 164, 260, 265, 266, 273, 276, 288, 290, 292),
    (147, 284, 480): (38, 41, 69, 74),
}


def forbidden_exact(targets):
    """Masks to exclude exactly on top of the universal per-row pair constraints."""
    return EXCLUDED[tuple(targets)]


def apply_envelope(enc, gate_specs, targets, nlines):
    """Forbid missing exact masks on symbolic line operands, including their zero bits."""
    rejected = forbidden_exact(targets)
    assert nlines == max(t.bit_length() for t in targets) and 0 not in rejected
    for left, right, _ in gate_specs:
        for _, bits in (left, right):
            assert len(bits) == nlines
            for mask in rejected:
                enc.clause(*(-bit if mask & (1 << i) else bit for i, bit in enumerate(bits)))


@cache
def row_preserving(targets):
    count = max(t.bit_length() for t in targets)
    classes = defaultdict(list)
    for column in range(count):
        classes[tuple((t >> column) & 1 for t in targets)].append(column)
    groups = tuple(classes.values())
    result = []
    for destinations in product(*(permutations(indices) for indices in groups)):
        perm = list(range(count))
        for indices, image in zip(groups, destinations):
            for source, dest in zip(indices, image):
                perm[source] = dest
        result.append(tuple(perm))
    return tuple(result)


@cache
def mask_map(perm):
    """Return the image of each mask under the map old position -> new position."""
    return tuple(sum(1 << target for i, target in enumerate(perm) if mask & (1 << i))
                 for mask in range(1 << len(perm)))


def relabel(masks, perm):
    table = mask_map(perm)
    return frozenset(table[m] for m in masks)


def stabilizer(masks, targets):
    """All permutations of lines preserving both the masks and the three targets."""
    masks = frozenset(masks)
    return tuple(p for p in row_preserving(tuple(targets)) if relabel(masks, p) == masks)


def physical_to_envelope(rows):
    source, targets, lines = project(rows, "actual")
    universal, check_targets, check_lines = project(rows, "universal")
    assert (targets, lines) == (check_targets, check_lines)
    envelope = set(universal) - set(forbidden_exact(targets))
    for perm in row_preserving(targets):
        mapped = relabel(source, perm)
        if mapped <= envelope:
            table = mask_map(perm)
            assert tuple(table[t] for t in targets) == targets
            return perm
    raise ValueError(f"No valid line relabeling for ordered rows {rows}")


def coverage():
    classes = defaultdict(list)
    totals = Counter()
    envelope_info = {}
    for rows in permutations(range(6), 3):
        masks, targets, lines = project(rows, "actual")
        source = frozenset(masks)
        universal = set(project(rows, "universal")[0])
        forbidden = set(forbidden_exact(targets))
        assert forbidden <= universal
        envelope = universal - forbidden
        witness = physical_to_envelope(rows)
        assert relabel(masks, witness) <= envelope
        # This check is deliberately over all raw masks so it also checks the
        # conjunction of the universal clauses with the exact-pattern exclusions.
        for m in range(1 << len(lines)):
            admissible = all((m & target).bit_count() <= 1 for target in targets)
            assert (m in envelope) == (admissible and m not in forbidden)
        key = min(tuple(sorted(relabel(source, p))) for p in row_preserving(targets))
        classes[len(lines), key].append(rows)
        totals[len(lines)] += 1
        envelope_info[len(lines)] = (len(envelope), len(stabilizer(envelope, targets)))
    by_shape = Counter(n for n, _ in classes)
    assert totals == {9: 108, 10: 12} and by_shape == {9: 18, 10: 9}
    assert envelope_info[9][0] == 32 and envelope_info[10][0] == 41
    print("Rows | ordered triples | physical bank classes | envelope masks | envelope automorphisms")
    for n in sorted(totals):
        print(n, totals[n], by_shape[n], *envelope_info[n])
    # An explicit permutation for each assignment is available via physical_to_envelope.
    return classes


if __name__ == "__main__":
    classes = coverage()
    if "--classes" in sys.argv[1:]:
        for (n, _), members in sorted(classes.items(), key=lambda item: item[1][0]):
            representative = members[0]
            masks, targets, _ = project(representative, "actual")
            group = stabilizer(masks, targets)
            print("rep", representative, "members", members, "nonidentity generators", group[1:])
