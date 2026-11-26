"""Replay the finite cube decoder on small graphs. Requires Python 3.10+."""
from itertools import combinations
from random import Random


def require(test, message):
    if not test:
        raise ValueError(message)


def union(words):
    out = 0
    for word in words:
        out |= word
    return out


def colors(rows, slack):
    """Greedy coloring within each weight; each color index is local to that weight."""
    tags = {}
    for word in rows:
        weight = word.bit_count()
        used = {color for other, (w, color) in tags.items()
                if w == weight and (word & ~other).bit_count() <= slack}
        color = 0
        while color in used:
            color += 1
        tags[word] = (weight, color)
    return tags


def dictionary_bits(tag_count, requests):
    """Produce witnessed separators for this instance, with singleton bits as a fallback."""
    missing = {(z, group) for group in requests for z in range(tag_count) if not group >> z & 1}
    codes = [0] * tag_count
    random = Random(1964)
    width = 0
    while missing:
        candidate = random.getrandbits(tag_count)
        covered = {(z, group) for z, group in missing if candidate >> z & 1 and not candidate & group}
        if not covered:
            z = min(missing)[0]
            candidate = 1 << z
            covered = {pair for pair in missing if pair[0] == z}
        for z in range(tag_count):
            if candidate >> z & 1:
                codes[z] |= 1 << width
        width += 1
        missing -= covered
    return codes, width


def verify(d, rows, cols, neighbors, compress=True):
    require(set(cols) == set(neighbors) and len(set(rows + cols)) == len(rows + cols),
            "addresses must inject into the cube")
    require(all(0 <= x < 1 << d for x in rows + cols), "address length")
    degree = max(map(len, neighbors.values()), default=0)
    radius = max(((x ^ c).bit_count() for c in cols for x in neighbors[c]), default=0)
    hull = {c: union(neighbors[c]) for c in cols}
    slack = max(((hull[c] & ~x).bit_count() for c in cols for x in neighbors[c]), default=0)
    require(slack <= 2 * degree * radius, "locality bound")
    tags = colors(rows, slack)
    ids = {tag: i for i, tag in enumerate(sorted(set(tags.values())))}
    index = {x: ids[tags[x]] for x in rows}
    requests = {c: union(1 << index[x] for x in neighbors[c]) for c in cols}
    count = len(ids)
    if compress:
        code, width = dictionary_bits(count, set(requests.values()))
    else:
        code, width = [1 << j for j in range(count)], count
    left = {x: x | (code[index[x]] << d) for x in rows}
    right = {c: hull[c] | (union(code[index[x]] for x in neighbors[c]) << d) for c in cols}
    # Complement each zero rectangle and intersect the resulting free unions, cell by cell.
    factors = [({x for x in rows if not left[x] >> bit & 1},
                {c for c in cols if right[c] >> bit & 1}) for bit in range(d + width)]
    # An independently constructed non-flat formula uses one binary equality test per slot.
    # The sentinel is outside the set of row tags, including on columns of smaller degree.
    bits = max(1, count.bit_length())
    slots = {}
    for c in cols:
        active = sorted({index[x] for x in neighbors[c]})
        slots[c] = active + [count] * (degree - len(active))
    for c in cols:
        for x in rows:
            in_slot = any(all(((not (index[x] >> j & 1)) or (symbol >> j & 1)) and
                              ((index[x] >> j & 1) or not (symbol >> j & 1))
                              for j in range(bits)) for symbol in slots[c])
            require((not (x & ~hull[c]) and in_slot) == (x in neighbors[c]), "slot formula")
            value = all(x in allowed_rows or c in allowed_cols for allowed_rows, allowed_cols in factors)
            require(value == (x in neighbors[c]), "formula cell mismatch")
    return len(rows) * len(cols), count, width


def main():
    # All edge subsets of every one of the twelve cube edges, including all isolated cases.
    rows = [x for x in range(8) if x.bit_count() % 2 == 0]
    cols = [x for x in range(8) if x.bit_count() % 2]
    cube = [(x, c) for x in rows for c in cols if (x ^ c).bit_count() == 1]
    checked = 0
    for mask in range(1 << len(cube)):
        adj = {c: set() for c in cols}
        for bit, (x, c) in enumerate(cube):
            if mask >> bit & 1:
                adj[c].add(x)
        checked += verify(3, rows, cols, adj, compress=False)[0]
    print(f"All 4,096 edge subsets of the 3-cube: {checked:,} formula cells.")

    # A Gray path uses one bit change per step and exercises repeated tags and both filters.
    path = [i ^ (i >> 1) for i in range(256)]
    adj = {path[i]: {path[j] for j in (i-1, i+1) if j < len(path)} for i in range(1, 256, 2)}
    cells, count, width = verify(8, path[::2], path[1::2], adj)
    require(count < 128 and width < 128, "path must exercise tag reuse and compression")
    print(f"256-vertex Gray path: {cells:,} formula cells, {count} tags, {width} extra bits.")

    # Variable branching in a binary address tree. A moving terminator marks the depth.
    level = [1]
    rows, cols, adj = [1], [], {}
    for depth in range(7):
        following = []
        for x in level:
            children = [x ^ (1 << depth) ^ (1 << (depth+1)), x | (1 << (depth+1))]
            if x % 7 == 4:
                children.pop()
            following.extend(children)
            for y in children:
                if depth % 2:
                    rows.append(y)
                    adj[x].add(y)
                else:
                    cols.append(y)
                    adj[y] = {x}
        level = following
    cells, _, _ = verify(8, rows, cols, adj)
    print(f"Irregular binary tree: {len(rows)+len(cols)} vertices, {cells:,} formula cells.")

    # The coarse mask alone admits 0; a reused tag alone admits a distant row.
    # All four rows are distinct from the column address.
    rows = [0, 3, 5, 48]
    tag = {0: 0, 3: 1, 5: 2, 48: 1}
    adj = {3, 5}
    hull = union(adj)
    require(not (0 & ~hull) and 0 not in adj, "containment-only control")
    require(tag[48] in {tag[x] for x in adj} and 48 not in adj, "tag-only control")
    require({x for x in rows if not x & ~hull and tag[x] in {tag[y] for y in adj}} == adj,
            "combined controls")
    # Exhaustively exercise the code promise over all small dictionaries, including the empty one.
    groups = {sum(1 << i for i in J) for k in range(4) for J in combinations(range(9), k)}
    codes, _ = dictionary_bits(9, groups)
    require(all((not codes[z] & ~union(codes[j] for j in range(9) if J >> j & 1)) == bool(J >> z & 1)
                for J in groups for z in range(9)), "disjunct code")
    print("Both omission controls and all 1,170 small tag membership tests passed.")


if __name__ == "__main__":
    main()
