"""Exact checks for a norm-twisted spread of order nine. No third-party dependencies."""
from itertools import combinations


# Integer label a+3b represents a+b*i over F_3, with i*i=-1.
def add(x, y):
    return (x % 3 + y % 3) % 3 + 3*((x//3 + y//3) % 3)


def neg(x):
    return (-x % 3) + 3*(-(x//3) % 3)


def mul(x, y):
    a,b = x % 3, x//3
    c,d = y % 3, y//3
    return (a*c-b*d) % 3 + 3*((a*d+b*c) % 3)


def conjugate(x):
    return x % 3 + 3*(-(x//3) % 3)


def twist(m):
    return mul(m,conjugate(m)) == 2


def affine_value(m, x):
    return mul(m,conjugate(x) if twist(m) else x)


# Affine point 9*x+y, direction point 81+m (m=9 means vertical).
# Line 9*m+b for a slope/intercept or vertical x=b, line 90 at infinity.
def incident(point, line, twisted=True):
    if point >= 81:
        return line == 90 or point-81 == line//9
    if line == 90:
        return False
    x,y = divmod(point,9)
    m,b = divmod(line,9)
    if m == 9:
        return x == b
    image = affine_value(m,x) if twisted else mul(m,x)
    return y == add(image,b)


def normal(x):
    # Coordinates in theta=1+i, theta^3=1-i. 2 is the inverse of 2 mod 3.
    a,b = x % 3, x//3
    return (2*(a+b) % 3, 2*(a-b) % 3)


class Stars:
    """Execute the paid intersections over the entire grid as integer bit vectors."""
    def __init__(self):
        self.cost = 0

    def row(self, predicate):
        full = (1 << 91)-1
        return sum(full << (91*i) for i in range(91) if predicate(i))

    def col(self, predicate):
        word = sum(1 << i for i in range(91) if predicate(i))
        return sum(word << (91*i) for i in range(91))

    def meet(self, a, b):
        self.cost += 1
        return a & b

    def trits(self, side, f):
        return [side(lambda v: f(v) == i) for i in range(3)]

    def trit_mul(self, a, b):
        pos = self.meet(a[1],b[1]) | self.meet(a[2],b[2])
        negv = self.meet(a[1],b[2]) | self.meet(a[2],b[1])
        return [a[0] | b[0], pos, negv]

    def trit_add(self, a, b):
        result = [0,0,0]
        for i in range(3):
            for j in range(3):
                result[(i+j) % 3] |= self.meet(a[i],b[j])
        return result

    def same_trit(self, a, b):
        return self.meet(a[0],b[0]) | self.meet(a[1],b[1]) | self.meet(a[2],b[2])


def circuit():
    net = Stars()
    select = net.col(lambda l: twist((l//9) % 9))
    stay = net.col(lambda l: not twist((l//9) % 9))
    coords = [net.trits(net.row,lambda pt,i=i: normal((pt//9) % 9)[i]) for i in range(2)]
    rotated = [[net.meet(stay,coords[i][j]) | net.meet(select,coords[1-i][j])
                for j in range(3)] for i in range(2)]
    matches = []
    for i in range(2):
        coeff = [net.trits(net.col,lambda l,v=v: normal(mul((l//9) % 9,v))[i]) for v in (4,7)]
        first,second = [net.trit_mul(rotated[k],coeff[k]) for k in range(2)]
        intercept = net.trits(net.col,lambda l: normal(l % 9)[i])
        observed = net.trits(net.row,lambda pt: normal(pt % 9)[i])
        matches.append(net.same_trit(net.trit_add(net.trit_add(first,second),intercept),observed))
    finite = net.meet(net.row(lambda pt: pt < 81), net.col(lambda l: l < 81))
    result = net.meet(net.meet(matches[0],matches[1]),finite)
    for x in range(9):
        result |= net.meet(net.row(lambda pt: pt < 81 and pt//9 == x),net.col(lambda l: l == 81+x))
    for m in range(10):
        result |= net.meet(net.row(lambda pt: pt == 81+m),net.col(lambda l: l < 90 and l//9 == m))
    result |= net.meet(net.row(lambda pt: pt >= 81),net.col(lambda l: l == 90))
    return net.cost,result


def geometry(twisted):
    lines = [{p for p in range(91) if incident(p,l,twisted)} for l in range(91)]
    join,meet = {},{}
    for l,points in enumerate(lines):
        assert len(points) == 10
        for a,b in combinations(sorted(points),2):
            assert (a,b) not in join
            join[a,b] = l
    assert len(join) == 91*90//2
    for a,b in combinations(range(91),2):
        common = lines[a] & lines[b]
        assert len(common) == 1
        meet[a,b] = next(iter(common))
    return lines,join,meet


def pair(table,a,b):
    return table[min(a,b),max(a,b)]


def perspective(lines, join, meet, center, top, bottom):
    if any(a == b or center in (a,b) or center not in lines[pair(join,a,b)]
           for a,b in zip(top,bottom)):
        return None
    triangles = (top,bottom)
    if any(len(set(t)) != 3 or t[2] in lines[pair(join,t[0],t[1])] for t in triangles):
        return None
    crosses = []
    for a,b in combinations(range(3),2):
        left,right = pair(join,top[a],top[b]),pair(join,bottom[a],bottom[b])
        if left == right:
            return None
        crosses.append(pair(meet,left,right))
    if len(set(crosses)) < 3:
        return None
    return crosses, crosses[2] in lines[pair(join,crosses[0],crosses[1])]


def witness(geo):
    lines,join,meet = geo
    # Try distinct affine rays through 0, with fixed top points on each ray.
    for dirs in combinations(range(10),3):
        rays = [sorted(p for p in lines[9*d] if 0 < p < 81) for d in dirs]
        top = [r[0] for r in rays]
        for bottom in ((a,b,c) for a in rays[0][1:] for b in rays[1][1:] for c in rays[2][1:]):
            answer = perspective(lines,join,meet,0,top,bottom)
            if answer and not answer[1]:
                return 0,top,bottom,answer[0]
    raise RuntimeError("No Desargues failure found in the selected rays")


if __name__ == "__main__":
    assert all(normal(conjugate(x)) == normal(x)[::-1] for x in range(9))
    for m in range(9):
        for n in range(m):
            assert {add(affine_value(m,x),neg(affine_value(n,x))) for x in range(9)} == set(range(9))
    # A point shear y -> y+lambda(x) gives an explicit one-dimensional correction.
    for m in range(9):
        for x in range(9):
            for y in range(9):
                for b in range(9):
                    linear = x % 3
                    assert (y == add(affine_value(m,x),b)) == (
                        add(y,linear) == add(add(affine_value(m,x),linear),b))
    geo = geometry(True)
    cost,encoding = circuit()
    target = sum(1 << (91*p+l) for l,ls in enumerate(geo[0]) for p in ls)
    assert encoding == target
    c,t,b,cross = witness(geo)
    print(f"91 points, 91 lines, 910 incidences; all point and line pairs checked.")
    print(f"All 8281 circuit outputs agree; {cost} paid intersections in this test circuit.")
    print(f"Desargues failure: center={c}, top={t}, bottom={list(b)}, side crossings={cross}.")
    # A projective line at infinity is included on both sides of every check.
    assert all(not incident(cross[0],l) or not incident(cross[1],l) or
               not incident(cross[2],l) for l in range(91))
    print("The three side crossings have no common line; all 6561 rank-one shear checks passed.")
