"""Eliminate unknown summands of a shared coefficient in the aggregate moment kernel."""
import argparse
import itertools
from collections import Counter, defaultdict
from functools import lru_cache
from math import prod

P = 65537
BIN = (1, 3, 3, 1)
INV_BIN = tuple(pow(x, -1, P) for x in BIN)


def det(matrix):
    """Determinant modulo P by row elimination, including singular specializations."""
    a = [row.copy() for row in matrix]
    ans = 1
    for j in range(len(a)):
        pivot = next((k for k in range(j, len(a)) if a[k][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            ans = -ans
        v = a[j][j]
        ans = ans * v % P
        inv = pow(v, -1, P)
        for k in range(j + 1, len(a)):
            if a[k][j]:
                s = a[k][j] * inv % P
                for i in range(j + 1, len(a)):
                    a[k][i] = (a[k][i] - s*a[j][i]) % P
    return ans


def norm_at_sum(total, equations):
    """Necessary scalar equation on total=sum x_i if d_i*x_i^m_i=n_i."""
    product = prod(d for m, d, n in equations) % P
    diag = total * product % P
    wraps = [n * prod(e[1] for j,e in enumerate(equations) if j != i) % P
             for i,(m,d,n) in enumerate(equations)]
    orders = tuple(m for m,d,n in equations)
    if all(m == 1 for m in orders):
        return (diag - sum(wraps)) % P
    size = prod(orders)
    a = [[0] * size for _ in range(size)]
    # Monomials in the unknown contributions, with exponents < orders.
    for col in range(size):
        a[col][col] = diag
        stride = 1
        for i, m in enumerate(orders):
            if col//stride % m + 1 == m:
                row = col - (m-1)*stride
                value = wraps[i]
            else:
                row = col + stride
                value = product
            a[row][col] = (a[row][col]-value) % P
            stride *= m
    return det(a)


def shared_constraint(s, incident, nodes, private):
    """Use two private coefficients of each contributing cube. Select the lowest degree."""
    choices = []
    for i,k in incident:
        pairs = list(itertools.combinations(private[i], 2))
        if not pairs:
            return None
        choices.append(pairs)

    def degree(pairs):
        d = sum(max(0,k-b,a-k) for (i,k),(a,b) in zip(incident,pairs))
        return (1+d)*prod(b-a for a,b in pairs)

    chosen = min(itertools.product(*choices),key=degree)
    def evaluate(values):
        equations = []
        for (i,k),(a,b) in zip(incident,chosen):
            ca = values[nodes[i][a]] * INV_BIN[a] % P
            cb = values[nodes[i][b]] * INV_BIN[b] % P
            m = b-a
            den = pow(ca,max(0,k-b),P)*pow(cb,max(0,a-k),P) % P
            num = pow(BIN[k],m,P)*pow(ca,max(0,b-k),P)*pow(cb,max(0,k-a),P) % P
            equations.append((m,den,num))
        return norm_at_sum(values[s],equations)
    return degree(chosen), evaluate


def private_constraints(nodes, private):
    # The slots h_j are divided by their binomial coefficients here.
    for i, indices in enumerate(private):
        for a,b,c in itertools.combinations(indices,3):
            def evaluate(values, arm=nodes[i], a=a,b=b,c=c):
                f = lambda j: values[arm[j]]*INV_BIN[j] % P
                return (pow(f(b),c-a,P)-pow(f(a),c-b,P)*pow(f(c),b-a,P)) % P
            yield c-a, evaluate
        if len(indices)==4:
            def mixed(values, arm=nodes[i]):
                a,b,c,d = (values[s] for s in arm)
                return (b*c-9*a*d) % P
            yield 2,mixed


def univariate(values):
    """Recover power coefficients from values at 0,...,degree by Newton differences."""
    degree = len(values)-1
    out = [0]*(degree+1)
    basis = [1]
    for i in range(degree+1):
        for j,b in enumerate(basis):
            out[j] = (out[j] + values[0]*b) % P
        values = [(b-a) % P for a,b in zip(values,values[1:])]
        inv = pow(i+1,-1,P)
        new = [0]*(len(basis)+1)
        for j,b in enumerate(basis):
            new[j] = (new[j]-i*b*inv) % P
            new[j+1] = b*inv % P
        # The term j+1 receives its x coefficient now and its -i coefficient next.
        basis = new
    while out and out[-1]==0:
        out.pop()
    return out


def poly_gcd(a,b):
    a = a.copy()
    b = b.copy()
    while b:
        inv = pow(b[-1],-1,P)
        while len(a)>=len(b):
            scale = a[-1]*inv % P
            shift = len(a)-len(b)
            for j,v in enumerate(b):
                a[j+shift]=(a[j+shift]-scale*v) % P
            while a and not a[-1]:
                a.pop()
        a,b=b,a
    return a


def span_full(rows, size):
    basis = {}
    for original in rows:
        row = original.copy()
        for j in range(size):
            if not row[j]:
                continue
            if j not in basis:
                inv = pow(row[j],-1,P)
                basis[j]=[v*inv%P for v in row[j:]]
                break
            s = row[j]
            row[j:]=[(v-s*w)%P for v,w in zip(row[j:],basis[j])]
        if len(basis)==size:
            return True
    return False


def certify(shape):
    nodes = [[(3-j)*a+j*b for j in range(4)] for a,b in shape]
    uses=defaultdict(list)
    for i,arm in enumerate(nodes):
        for j,s in enumerate(arm):
            uses[s].append((i,j))
    dims = len(uses)-8
    if dims<=0:
        return "Vandermonde"
    if dims>3:
        raise ValueError("expected an overlapping support")
    private=[[j for j,s in enumerate(arm) if len(uses[s])==1] for arm in nodes]
    weights={s:pow(prod(s-t for t in uses if s!=t),-1,P) for s in uses}
    @lru_cache(None)
    def at(u,v,w):
        return {s:(u+s*(v+s*w))*h%P for s,h in weights.items()}
    constraints=list(private_constraints(nodes,private))
    for s, incident in uses.items():
        if len(incident)>1:
            con=shared_constraint(s,incident,nodes,private)
            if con is not None:
                constraints.append(con)
    constraints.sort(key=lambda item:item[0])
    if dims==1:
        return "scalar" if any(f(at(1,0,0)) for _,f in constraints) else None
    if dims==2:
        common=[]
        infinity=False
        for degree,f in constraints:
            vals=[f(at(1,x,0)) for x in range(degree+1)]
            g=univariate(vals)
            inf=f(at(0,1,0))
            if (g[-1] if len(g)==degree+1 else 0)!=inf:
                raise ArithmeticError("homogeneous degree or interpolation mismatch")
            infinity |= bool(inf)
            common=poly_gcd(common,g)
            if len(common)==1 and infinity:
                return "binary"
        return None
    # The remaining eleven-node cases use projective degree-three/four/...
    # forms on a triangular evaluation grid, including the mixed identities.
    for D in range(3,8):
        grid=[(x,y) for x in range(D+1) for y in range(D+1-x)]
        def rows():
            for degree,f in constraints:
                if degree>D: continue
                vals=[f(at(1,x,y)) for x,y in grid]
                for i in range(D-degree+1):
                    for j in range(D-degree+1-i):
                        yield [v*pow(x,i,P)*pow(y,j,P)%P for v,(x,y) in zip(vals,grid)]
        if span_full(rows(),len(grid)):
            return "ternary"
    return None


def controls():
    for degree in range(7):
        coefficients=list(range(1,degree+2))
        sampled=[sum(c*x**j for j,c in enumerate(coefficients))%P for x in range(degree+1)]
        assert univariate(sampled)==coefficients
    # Known decompositions must make the norm zero, including mixed square
    # and cube powers and a specialization with a vanishing denominator.
    for degrees in ((1,1),(2,1),(2,3),(1,2,3)):
        roots=(2,5,9)[:len(degrees)]
        eq=[(m,i+1,(i+1)*r**m%P) for i,(m,r) in enumerate(zip(degrees,roots))]
        assert norm_at_sum(sum(roots),eq)==0
    assert norm_at_sum(9,[(1,2,6),(1,4,20)])!=0
    assert norm_at_sum(9,[(2,0,0),(1,4,20)])==0
    print("PASS interpolation and known-root elimination controls")


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--control-mod11',action='store_true',help='check the positive control only')
    parser.add_argument('cases',nargs='?')
    parser.add_argument('survivors',nargs='?')
    args=parser.parse_args()
    if args.control_mod11:
        P=11
        INV_BIN=tuple(pow(x,-1,P) for x in BIN)
        if certify(((0,1),(0,10),(1,2))) is not None:
            raise ValueError("characteristic-11 witness incorrectly excluded")
        print("PASS shared-coefficient elimination retains the characteristic-11 witness")
        raise SystemExit(0)
    if not args.cases or not args.survivors:
        parser.error('provide the cases and survivors paths')
    controls()
    groups=Counter()
    with open(args.cases) as source,open(args.survivors,'w') as sink:
        for line in source:
            ends=tuple(map(int,line.split()))
            if len(ends)!=6: raise ValueError(line)
            shape=tuple(zip(ends[::2],ends[1::2]))
            verdict=certify(shape)
            groups[max(ends)>=33,verdict or 'unresolved']+=1
            if not verdict:
                sink.write(' '.join(map(str,ends))+'\n')
    for key,v in sorted(groups.items()):
        print('spans 33-64' if key[0] else 'spans 1-32',key[1],v)
