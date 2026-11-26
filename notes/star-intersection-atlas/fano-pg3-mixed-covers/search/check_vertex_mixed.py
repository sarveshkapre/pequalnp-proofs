"""Independent design search with signed words and a column antichain test."""
from collections import Counter
from itertools import combinations, product
from mixed_row_families import representatives


WORDS = list(product((-1,0,1), repeat=4))
def subset_face(a,b):
    return all(v == -1 or u == v for u,v in zip(a,b))


def compatible(a,b):
    return all(u == -1 or v == -1 or u == v for u,v in zip(a,b))


def set_bits(bits):
    while bits:
        bit = bits & -bits
        yield bit.bit_length()-1
        bits ^= bit


def has_antichain(domains, forbidden):
    if not domains:
        return True
    d = min(domains, key=int.bit_count)
    if not d:
        return False
    rest = domains.copy()
    rest.remove(d)
    return any(has_antichain([m & ~forbidden[c] for m in rest], forbidden)
               for c in set_bits(d))


def has_two_sided(rows,blocks,domains,hits,forbidden):
    # Choose a legal witness word afresh at every nonincidence.
    assignments = {}
    def visit():
        for col,c in assignments.items():
            for p,row in enumerate(rows):
                if p in blocks[col]:
                    continue
                wanted=hits[row] & hits[WORDS[c]]
                for point in blocks[col]:
                    wanted &= ~hits[rows[point]]
                for other,k in assignments.items():
                    if p in blocks[other]:
                        wanted &= ~hits[WORDS[k]]
                if not wanted:
                    return False
        if len(assignments)==len(blocks):
            return True
        prohibited=0
        for c in assignments.values():
            prohibited |= forbidden[c]
        options,col=min(((domains[i]&~prohibited,i) for i in range(len(blocks)) if i not in assignments),
                        key=lambda pair:pair[0].bit_count())
        for c in set_bits(options):
            assignments[col]=c
            if visit():
                return True
            del assignments[col]
        return False
    return visit()


def check(family):
    real = [tuple(i >> j & 1 for j in range(4)) for i in range(16)]
    rows = [next(w for w in WORDS
                 if sum(1 << i for i,v in enumerate(real) if compatible(w,v)) == f)
            for f in family]
    hits = {w: sum(1 << i for i,v in enumerate(WORDS) if compatible(w,v))
            for w in WORDS}
    forbidden = [sum(1<<j for j,v in enumerate(WORDS) if subset_face(v,w) or subset_face(w,v))
                 for w in WORDS]
    options = []
    signatures = []
    blocks = []
    pair_ids = {pair:i for i,pair in enumerate(combinations(range(13),2))}
    by_pair = [0]*78
    for block in combinations(range(13),4):
        safe = (1<<81)-1
        for p in block:
            safe &= ~hits[rows[p]]
        choices = 0
        for i in set_bits(safe):
            connectors = safe & hits[WORDS[i]]
            if all(connectors & hits[v] for p,v in enumerate(rows) if p not in block):
                choices |= 1 << i
        if choices:
            pair_bits = sum(1<<pair_ids[pair] for pair in combinations(block,2))
            for pair in set_bits(pair_bits):
                by_pair[pair] |= 1 << len(options)
            options.append(choices)
            signatures.append(pair_bits)
            blocks.append(block)
    collision = []
    for pairs in signatures:
        forbid = 0
        for p in set_bits(pairs):
            forbid |= by_pair[p]
        collision.append(forbid)
    tally = Counter()
    def visit(remaining,candidates,chosen):
        if not remaining:
            assert len(chosen)==13
            tally["designs"]+=1
            if has_antichain([options[i] for i in chosen],forbidden):
                tally["column_antichain"]+=1
                if has_two_sided(rows,[blocks[i] for i in chosen],[options[i] for i in chosen],hits,forbidden):
                    tally["two_sided"]+=1
            return
        choices = min((by_pair[p]&candidates for p in set_bits(remaining)), key=int.bit_count)
        for k in set_bits(choices):
            visit(remaining ^ signatures[k],candidates & ~collision[k],chosen+[k])
    visit((1<<78)-1,(1<<len(options))-1,[])
    return len(options),dict(tally)


if __name__=="__main__":
    for i,family in enumerate(representatives(0)):
        print(i,len(family),check(family),flush=True)
