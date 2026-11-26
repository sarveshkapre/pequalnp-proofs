"""Independent truth-table verifier for fan-in-two monotone 3 by 3 matching circuits.

Python 3.10 or later, standard library only. All gates in every prefix are
explicit binary gates. No memoization or symmetry reduction of prefixes.
"""
from functools import cache
from itertools import combinations, permutations, product



def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def prime(terms):
    result = []
    for mask in sorted(set(terms), key=lambda t: (t.bit_count(), t)):
        if all((r & mask) != r for r in result):
            result.append(mask)
    return tuple(sorted(result))


def canonical(f):
    # Identity key: verify every actual labeled cofactor and every labeled prefix.
    return f


def support(f):
    return tuple(bits(sum(1 << i for i in range(9) if any(m & (1 << i) for m in f))))


@cache
def condition(f, i, bit):
    b = 1 << i
    return prime(t & ~b for t in f if bit or not (t & b))


@cache
def lower(f):
    return known[canonical(f)]


class Check:
    def __init__(self,f):
        self.f = f
        self.ids = support(f)
        self.n = len(self.ids)
        all_graphs = range(1 << self.n)
        self.top = (1 << len(all_graphs)) - 1
        graph = [sum(1 << self.ids[i] for i in bits(m)) for m in all_graphs]
        yes = [any(m & t == t for t in f) for m in graph]
        self.target = sum(1 << m for m in all_graphs if yes[m])
        self.pos = [m for m in all_graphs if yes[m] and all(not yes[m ^ (1<<i)] for i in bits(m))]
        self.neg = [m for m in all_graphs if not yes[m] and all(yes[m | (1<<i)] for i in bits((len(all_graphs)-1)^m))]
        self.raw = tuple(sum(1<<m for m in all_graphs if m & (1<<i)) for i in range(self.n))
        self.every = (1 << (len(self.pos) * len(self.neg))) - 1
        self.sections = []
        for arity in (1,2):
            for axes in combinations(range(self.n),arity):
                for assignment in product((0,1),repeat=arity):
                    fixed = sum((1<<i)*v for i,v in zip(axes,assignment))
                    fixed_mask = sum(1<<i for i in axes)
                    keep = sum(1<<m for m in all_graphs if (m & fixed_mask)==fixed)
                    sub=f
                    for i,v in zip(axes,assignment): sub=condition(sub,self.ids[i],v)
                    if not support(sub): continue
                    self.sections.append((lower(sub), keep, {0,keep}|{x & keep for x in self.raw}))
        self.sections.sort(key=lambda x:-x[0])
        self.cover_cache = {}
        self.visits = 0

    def cover(self,wire):
        if wire not in self.cover_cache:
            holes = sum(1<<i for i,m in enumerate(self.neg) if not wire>>m&1)
            self.cover_cache[wire]=sum(holes<<(i*len(self.neg)) for i,m in enumerate(self.pos) if wire>>m&1)
        return self.cover_cache[wire]

    def excludes(self, prefix, sinks, goal):
        all_wires = self.raw+prefix
        # Source masks for every original positive/negative pair. A valid
        # crossing-wire set must hit every one of these masks.
        pair_masks = []
        def code(point):
            return sum(((wire >> point) & 1) << i for i,wire in enumerate(all_wires))
        p_codes = [code(point) for point in self.pos]
        n_codes = [code(point) for point in self.neg]
        for a in p_codes:
            for b in n_codes: pair_masks.append(a & ~b)
        wire_bits = (1 << len(all_wires)) - 1
        for lower_bound, keep, available in self.sections:
            # Count how many distinct, novel restricted prefix values need gates.
            retained = {wire & keep for wire in prefix} - available
            vanish = len(prefix) - len(retained)
            const_idx = [i for i,wire in enumerate(all_wires) if wire&keep in (0,keep)]
            mandatory = len(set(const_idx)&sinks)
            need = goal - (lower_bound + vanish + mandatory)
            if need<=0: return True
            optional = set(const_idx)-sinks
            if need>len(optional): continue
            forced_sources = wire_bits ^ sum(1 << i for i in optional)
            critical_pairs = [m for m in pair_masks if not (m & forced_sources)]
            if not critical_pairs: continue
            for extra in combinations(optional,need-1):
                trial = sum(1 << i for i in extra)
                if all(m & trial for m in critical_pairs): break
            else: return True
        return False

    def proof(self,prefix,sinks,goal,depth):
        self.visits+=1
        wires = self.raw+prefix
        if self.target in wires: return len(prefix)>=goal
        if self.excludes(prefix,sinks,goal): return True
        if len(prefix)==depth: return False
        for i,j in combinations(range(len(wires)),2):
            for new in (wires[i] & wires[j], wires[i] | wires[j]):
                if new in wires or new in (0,self.top):continue
                if not self.proof(prefix+(new,), (sinks-{i,j})|{len(wires)}, goal,depth): return False
        return True


def main():
    root=prime(sum(1<<(3*r+p[r]) for r in range(3)) for p in permutations(range(3)))
    forms={root}; pending=[root]
    while pending:
        f=pending.pop()
        for i in support(f):
            for v in (0,1):
                nxt=canonical(condition(f,i,v))
                if nxt not in forms: forms.add(nxt); pending.append(nxt)
    print('class count',len(forms), flush=True)
    for f in sorted(forms,key=lambda m:(len(support(m)),m)):
        n=len(support(f)); val=max(0,n-1); last=0
        if n>=3:
            ck=Check(f)
            for goal in range(val+1,15):
                for depth in range(1,min(goal-1,4)+1):
                    if ck.proof((),set(),goal,depth): break
                else:break
                val=goal;last=depth
            if n>=8: print(n,f,'bound',val,'depth',last,'visits',ck.visits,flush=True)
        known[f]=val
    print('root',known[root],flush=True)
    assert known[canonical(root)]==14


known={}
if __name__=='__main__': main()
