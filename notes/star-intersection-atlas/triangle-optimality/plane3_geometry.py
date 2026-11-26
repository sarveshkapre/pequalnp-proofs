"""Print PG(2,3) and its point and line permutations for the two distance checks."""
from itertools import product


def normalize(vector):
    scale = next((x % 3 for x in vector if x % 3), 0)
    return tuple((x * scale) % 3 for x in vector)


def main():
    points = [v for v in product(range(3), repeat=3) if any(v) and normalize(v) == v]
    index = {point: i for i, point in enumerate(points)}
    lines = [frozenset(i for i, point in enumerate(points)
                       if sum(x * y for x, y in zip(point, normal)) % 3 == 0)
             for normal in points]
    line_index = {line: j for j, line in enumerate(lines)}
    print(*(sum(1 << j for j, line in enumerate(lines) if i in line)
            for i in range(13)))
    actions = set()
    for matrix in product(range(3), repeat=9):
        if next((x for x in matrix if x), 0) != 1:
            continue
        a, b, c, d, e, f, g, h, k = matrix
        if (a*(e*k-f*h) - b*(d*k-f*g) + c*(d*h-e*g)) % 3 == 0:
            continue
        perm = tuple(index[normalize((a*x+b*y+c*z, d*x+e*y+f*z, g*x+h*y+k*z))]
                     for x, y, z in points)
        assert len(set(perm)) == 13 and perm not in actions
        actions.add(perm)
        line_perm = [line_index[frozenset(perm[i] for i in line)] for line in lines]
        assert len(set(line_perm)) == 13
        print(*perm, *line_perm)
    assert len(actions) == 5616


if __name__ == "__main__":
    main()
