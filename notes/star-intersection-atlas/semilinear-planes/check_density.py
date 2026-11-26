"""Recover transformed slopes by Moore interpolation, then check every pair independently."""
from itertools import combinations, product


class Field:
    def __init__(self, modulus):
        self.d = len(modulus)-1
        self.q = 3**self.d
        words = [tuple((v//3**j) % 3 for j in range(self.d)) for v in range(self.q)]

        def encode(word):
            return sum((c % 3)*3**j for j,c in enumerate(word))

        self.plus = [[encode([u+v for u,v in zip(a,b)]) for b in words] for a in words]
        self.neg = [encode([-c for c in a]) for a in words]
        self.times = []
        for a in words:
            row = []
            for b in words:
                coeff = [0]*(2*self.d-1)
                for j,u in enumerate(a):
                    for k,v in enumerate(b):
                        coeff[j+k] += u*v
                for j in range(len(coeff)-1,self.d-1,-1):
                    t = coeff[j] % 3
                    for k,c in enumerate(modulus):
                        coeff[j-self.d+k] -= t*c
                row.append(encode(coeff[:self.d]))
            self.times.append(row)
        self.inv = [0] + [row.index(1) for row in self.times[1:]]
        assert all(len(set(row)) == self.q for row in self.times[1:])

    def power(self,a,n):
        v = 1
        while n:
            if n % 2:
                v = self.times[v][a]
            n //= 2
            a = self.times[a][a]
        return v

    def sum(self, values):
        v = 0
        for t in values:
            v = self.plus[v][t]
        return v

    def subtract(self,a,b):
        return self.plus[a][self.neg[b]]

    def interpolate(self,action,powers):
        # Solve on the polynomial basis; subsequently test on every field element.
        d = self.d
        mat = [powers[3**j][:] + [action[3**j]] for j in range(d)]
        for k in range(d):
            pivot = next(j for j in range(k,d) if mat[j][k])
            mat[k],mat[pivot] = mat[pivot],mat[k]
            inv = self.inv[mat[k][k]]
            mat[k] = [self.times[inv][a] for a in mat[k]]
            for j in range(d):
                if j != k:
                    factor = mat[j][k]
                    mat[j] = [self.subtract(a,self.times[factor][b]) for a,b in zip(mat[j],mat[k])]
        coeff = [r[-1] for r in mat]
        assert all(self.sum(self.times[a][b] for a,b in zip(coeff,powers[x])) == action[x]
                   for x in range(self.q))
        return coeff


def verify(modulus):
    f = Field(modulus)
    d,q = f.d,f.q
    powers = [[f.power(x,3**j) for j in range(d)] for x in range(q)]
    trace = [f.sum(row) for row in powers]
    assert set(trace) == {0,1,2}
    u = next(x for x in range(1,q) if trace[x] == 0)
    shear = [f.plus[x][f.times[u][trace[x]]] for x in range(q)]
    assert len(set(shear)) == q
    slopes, coefficients = [], []
    for m in range(q):
        norm = f.power(m,(q-1)//2)
        exponent = int(norm == 2)
        values = [shear[f.times[m][powers[x][exponent]]] for x in range(q)]
        slopes.append(values)
        coefficients.append(f.interpolate(values,powers))
    hist = [0]*(d+1)
    for m,n in combinations(range(q),2):
        assert len({f.subtract(a,b) for a,b in zip(slopes[m],slopes[n])}) == q
        nonzero = sum(a != b for a,b in zip(coefficients[m],coefficients[n]))
        hist[nonzero] += 1
        assert nonzero >= d-2
    print(f"GF({q}), degree {d}: {q*(q-1)//2} permuting differences; support histogram {hist}")


def irreducible(degree):
    def divides(g,h):
        r = list(h)
        for j in range(len(r)-len(g),-1,-1):
            v = r[j+len(g)-1] % 3
            for i,c in enumerate(g):
                r[j+i] -= v*c
        return all(c % 3 == 0 for c in r)

    divisors = [g+(1,) for t in range(1,degree//2+1) for g in product(range(3),repeat=t)]
    for poly in product(range(3),repeat=degree):
        candidate = poly+(1,)
        if candidate[0] and not any(divides(g,candidate) for g in divisors):
            return candidate
    raise RuntimeError("No irreducible polynomial found")


def maximal_hall(k):
    # The norm to the index-two subfield chooses the conjugation. Recover the
    # coefficients from values. Their predicted sign formula is never used.
    f = Field(irreducible(2*k))
    q,d = f.q,f.d
    powers = [[f.power(x,3**j) for j in range(d)] for x in range(q)]
    shear = [f.plus[x][f.sum(row)] for x,row in enumerate(powers)]
    assert len(set(shear)) == q
    coefficients = []
    for m in range(q):
        norm = f.power(m,3**k+1)
        branch = k if norm == 1 else 0
        values = [shear[f.times[m][powers[x][branch]]] for x in range(q)]
        coefficients.append(f.interpolate(values,powers))
    for j in range(d):
        assert {c[j] for c in coefficients} == set(range(q))
    for a,b in combinations(coefficients,2):
        assert all(x != y for x,y in zip(a,b))
    print(f"Hall order {q}: all {d} coefficient maps permute the field;"
          f" all {q*(q-1)//2} slope differences have full support.")


if __name__ == "__main__":
    for modulus in ([1,0,1], [1,2,0,1], [2,1,0,0,1]):
        verify(modulus)
    for k in (2,3):
        maximal_hall(k)
