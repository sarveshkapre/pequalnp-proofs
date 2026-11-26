from pathlib import Path
import sys
from collections import Counter
from itertools import combinations_with_replacement
sys.path.insert(0, str(Path(__file__).resolve().parent))
import independent as d

width = 4
universe = range(1 << width)
raw = tuple(sum(1 << m for m in universe if m & (1 << i)) for i in range(width))
top = (1 << len(universe)) - 1
minimum = {0:0, top:0, **{x:0 for x in raw}}
frontier = {frozenset(raw)}
for count in range(1,8):
    next_layer = set()
    for signals in frontier:
        for a,b in combinations_with_replacement(signals,2):
            for x in (a & b, a | b):
                if x in signals: continue
                minimum.setdefault(x,count)
                if count < 7: next_layer.add(signals | {x})
    frontier = next_layer

def mins(tt):
    return d.prime(m for m in universe if tt & (1 << m))

# All these generated truth tables have a known exact cost under binary gates
# except the constants (given free here, which does not affect nonconstant targets).
# Include their cofactors in topological order so all induction premises are available.
known_costs = {mins(tt): cost for tt,cost in minimum.items()}
for f in sorted(known_costs,key=lambda t:(len(d.support(t)),t)):
    variables = len(d.support(f)); lower = max(0, variables-1)
    if variables >= 3:
        search = d.Check(f)
        for goal in range(lower+1,known_costs[f]+2):
            if not search.proof((),set(),goal,min(4,goal-1)): break
            lower = goal
    assert lower <= known_costs[f], (f,lower,known_costs[f])
    d.known[f] = lower
print('Tested known optima on all attainable 4-input truth tables through 7 gates:',len(known_costs))
print('Counts by exact gate cost (constants supplied free for this control):',sorted(Counter(known_costs.values()).items()))
