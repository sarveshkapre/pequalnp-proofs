"""Check all row choices, physical inputs, sharp constructions, and counting cases."""
from itertools import combinations, permutations

from two_rows_sat import MASKS, ROWS, keep_pairs, shapes, tests

GRID = (29,225,1793,294,586,1170)
BUNDLES = (3,40,1064,272,336,516,644,48,560,264,392,68,1092)


def negative(points, lines):
    return (points & 7 != 7 and points & 56 != 56
            and all((lines & row).bit_count() <= 2 for row in GRID+BUNDLES)
            and not any(points >> i & 1 and lines & row for i,row in enumerate(GRID)))


def physical_columns():
    count = 1 << 17
    full = (1 << count)-1
    raw = []
    for j in range(17):
        step = 1 << j
        raw.append((full // ((1 << (2*step))-1)) * ((1 << step)-1) << step)
    bank = list(raw)
    for mask in BUNDLES:
        bank.append(union(raw[6+i] for i in range(11) if mask >> i & 1))
    return raw,bank


def union(values):
    total = 0
    for v in values:
        total |= v
    return total


def layout(pair, kept, leak, bank):
    values = list(bank)

    def gate(is_and, a, b):
        values.append(values[a] & values[b] if is_and else values[a] | values[b])
        return len(values)-1

    def join(ws):
        first,*rest=ws
        for other in rest:
            first=gate(False, first, other)
        return first

    terms = []
    for p in range(6):
        if p not in pair:
            ls = [6+i for i in range(11) if GRID[p] >> i & 1]
            terms.append(gate(True,p,join(ls)))
    assert len(values)==46
    rows = []
    for p in pair:
        ls = [6+l for pp,l in kept if pp==p]
        part = join(ls)
        if leak and p==pair[0]:
            other = [i for i in range(6) if i//3 == p//3 and i!=p]
            part = gate(False,part,gate(True,*other))
        rows.append(gate(True,p,part))
    terms.append(join(rows))
    out = join(terms)
    return len(values)-30,values[out]


def all_labellings():
    # Include all eight flags and every downward-closed negative used by the proof.
    # The third point, if present, is the remaining member of the rebuilt pair's side.
    seen=checked=0
    for a,b in permutations(range(6),2):
        same = a//3 == b//3
        q = next((p for p in range(6) if same and p//3==a//3 and p not in (a,b)),None)
        common, = [l for l in range(11) if GRID[a] & GRID[b] & (1 << l)]
        left = [l for l in range(11) if l!=common and GRID[a] >> l & 1]
        right = [l for l in range(11) if l!=common and GRID[b] >> l & 1]
        for x in permutations(left):
            for y in permutations(right):
                seen+=1
                order = (common,*x,*y)
                for active in range(4):
                    pp = (active & 1) << a | ((active >> 1) & 1) << b
                    for m in range(128):
                        if m.bit_count()>2:
                            continue
                        physical = sum(1 << l for i,l in enumerate(order) if m >> i & 1)
                        hit = any(active >> i & 1 and m & row for i,row in enumerate(ROWS))
                        if not hit:
                            assert negative(pp,physical)
                            if same and not m&1 and active!=3:
                                assert negative(pp | (1 << q),physical)
                        if active.bit_count()==1 and m.bit_count()==1:
                            assert hit==bool(physical & GRID[a if active==1 else b])
                        checked+=1
    assert seen==1080
    print(f"{checked} signed-pattern checks across {seen} physical row and line labellings.")


def check():
    all_labellings()
    raw,bank=physical_columns()
    all_flags = {(r,l) for r in range(6) for l in range(11) if GRID[r] >> l & 1}
    flags = sum(1 << ((1 << r) | (1 << (6+l))) for r,l in all_flags)
    rejected = sum(1 << (p | (m << 6)) for p in range(64) for m in range(2048) if negative(p,m))
    assert flags.bit_count()==24 and rejected.bit_count()==1072
    projected=layouts=0
    for a,b in combinations(range(6),2):
        common, = [l for l in range(11) if GRID[a] & GRID[b] & (1 << l)]
        order = [common] + [l for r in (a,b) for l in range(11) if l!=common and GRID[r] >> l & 1]
        physical_masks = {1 << l for l in range(11)} | set(BUNDLES)
        for r in range(6):
            if r not in (a,b):
                physical_masks |= {m for m in range(2048) if m & GRID[r] == m}
        for m in physical_masks:
            assert sum(((m >> l) & 1) << j for j,l in enumerate(order)) in MASKS
        same = a//3 == b//3
        third = next((i for i in range(6) if same and i//3==a//3 and i not in (a,b)),None)
        for shape in shapes(5):
            for q,p,m,goal in tests(keep_pairs(shape)):
                if q and not same:
                    continue
                pp = (p & 1) << a | ((p >> 1) & 1) << b
                if q:
                    pp |= 1 << third
                lines = sum(1 << l for i,l in enumerate(order) if m >> i & 1)
                assert not any(pp >> i & 1 and GRID[i] & lines for i in range(6) if i not in (a,b))
                if goal and q:
                    assert pp in (7,56) and lines==0
                elif goal:
                    assert (pp.bit_length()-1,lines.bit_length()-1) in all_flags
                else:
                    assert negative(pp,lines)
                projected+=1
        active = sorted((r,l) for r,l in all_flags if r in (a,b))
        fixed = union(raw[r] & raw[6+l] for r,l in all_flags if r not in (a,b))
        side = 3*(a//3)
        triple = raw[side] & raw[side+1] & raw[side+2]
        for k in range(5,9):
            for kept in combinations(active,k):
                target = fixed | union(raw[r] & raw[6+l] for r,l in kept)
                for leak in (False, True):
                    gates,value=layout((a,b),kept,leak,bank)
                    assert value == (target | (triple if leak else 0))
                    assert not (value & rejected) and (value & flags).bit_count()==16+k
                    assert gates==21+k+2*leak and bool((value >> 63)&1)==leak
                    layouts+=1
    assert layouts==2790
    print(f"{projected} physical test projections; {layouts} gate lists on all 131,072 inputs each.")
    flags8=[(p,1 << l) for p,row in zip((1,2),ROWS) for l in range(7) if row >> l & 1]
    for k in range(5,9):
        seen=set()
        lows=[]
        for selected in combinations(flags8,k):
            kept=set(selected)
            profiles=sorted((int((p,1) in kept),sum(r==p and m!=1 for r,m in kept)) for p in (1,2))
            seen.add("".join(f"{c}{n}" for c,n in profiles))
            cross={(i,j) for i in (1,2,3) for j in (4,5,6)
                   if (1,1 << i) in kept or (2,1 << j) in kept}
            lows.append(len(cross))
            if k>=6:
                # Plus two necessary point inputs; the augmented test also needs q.
                assert len(cross)+2 > k+1 and len(cross)+3 > k+3
        assert seen==set(shapes(k))
        print(f"{k} kept pairs: {len(lows)} labelled subsets, {len(seen)} shapes, at least {min(lows)} cross masks.")


if __name__=="__main__":
    check()
