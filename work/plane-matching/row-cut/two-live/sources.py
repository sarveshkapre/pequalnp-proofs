"""Enumerate physical line sources surviving the first core lower bound."""
from itertools import combinations
from cores import ROWS, bits, geometry, projected

def survivors(rows):
    points, union, core, bank = geometry(rows)
    pos, neg = projected(points, union)
    # Compare each flag with each physical negative containing the same point.
    clauses=set()
    for x in pos:
        for y in neg:
            if (x & 63) & ~y:
                continue
            clauses.add(sum(1<<i for i,m in enumerate(bank) if (x>>6)&m and not (y>>6)&m))
    minimal=sorted((x for x in clauses if not any(c!=x and c&x==c for c in clauses)),
                   key=lambda x:(x.bit_count(),x))
    assert 0 not in minimal
    # The 3+1 core needs twelve gates; the 2+2 core needs fifteen.
    cap = 6 if core.bit_count()==4 else 3
    vanishing = sum(1<<i for i,m in enumerate(bank) if not m&core)
    size=15 # four points plus line wires, at most 19 distinct inputs
    seen=set()
    answers=set()
    def visit(selected):
        if selected in seen or selected.bit_count()>size or (selected&vanishing).bit_count()>cap:
            return
        seen.add(selected)
        clause=next((c for c in minimal if not c&selected),0)
        if clause:
            for bit in bits(clause):
                visit(selected|bit)
        else:
            high = [i for i in range(len(bank)) if not selected>>i&1]
            # Extend this hitting set in every way within both budgets.
            def extend(start, used):
                answers.add(used)
                if used.bit_count() == size:
                    return
                for j in range(start,len(high)):
                    b=1<<high[j]
                    if not b&vanishing or (used&vanishing).bit_count()<cap:
                        extend(j+1,used|b)
            extend(0,selected)
    visit(0)
    return bank,answers

if __name__ == "__main__":
    from collections import Counter
    for rs in combinations(range(6),4):
        bank,ans=survivors(rs)
        print(rs,len(ans),sorted(Counter(s.bit_count() for s in ans).items()),flush=True)
