"""Compare direct gate evaluation to the bounded-depth rectangle construction."""
from itertools import product
from random import Random


def compiled(blocks, rows, cols, domain):
    """Evaluate the formula and return its cost and depth, including padded gates."""
    width = len(blocks)
    assert width and not width & (width-1)
    g = len(blocks[0])
    assert all(len(block) == g for block in blocks)
    result = domain
    gates = 0
    for block in blocks:
        word = 0
        for choices in product((0, 1), repeat=g):
            row, col = rows, cols
            for arms, side in zip(block, choices):
                add_row, add_col = arms[side]
                row |= add_row
                col |= add_col
            word |= (~row & domain) & (~col & domain)
            gates += 1
        result &= word
    return result, gates+width-1, width.bit_length()


def strips(nr, nc):
    def union(mask, row):
        return sum(1 << (i*nc+j) for i in range(nr) for j in range(nc)
                   if mask >> (i if row else j) & 1)
    return list(product([union(i,True) for i in range(1 << nr)],
                        [union(j,False) for j in range(1 << nc)]))


def direct(gates, raw):
    val = raw[0] | raw[1]
    for (r,s),(t,u) in gates:
        val |= (r|s) & (t|u)
    return val


if __name__ == '__main__':
    small = strips(2,2)
    arms = list(product(small, repeat=2))
    count = 0
    for a, b in product(arms, repeat=2):
        want = 15 ^ direct([a,b], (0,0))
        assert compiled([[a,b]], 0, 0, 15) == (want, 4, 1)
        assert compiled([[a],[b]], 0, 0, 15) == (want, 5, 2)
        count += 1
    print(f'{count} ordered 2-gate sources on the 2 by 2 grid checked at both depths')
    rng = Random(65536)
    raw = strips(4,5)
    empty_gate = ((0,0), (0,0))
    for trial in range(600):
        k = trial % 13
        gates = [(rng.choice(raw),rng.choice(raw)) for _ in range(k)]
        extra = rng.choice(raw) if trial % 3 else (0,0)
        domain = (1 << 20)-1
        for w in (1,2,4,8):
            g = (k+w-1)//w
            pad = gates + [empty_gate]*(g*w-k)
            blocks = [pad[t*g:(t+1)*g] for t in range(w)]
            want = domain ^ direct(gates,extra)
            assert compiled(blocks,*extra,domain) == (want,w*(2**g+1)-1,w.bit_length())
    print('600 padded 4 by 5 sources at four block widths, including output stars and k=0')
