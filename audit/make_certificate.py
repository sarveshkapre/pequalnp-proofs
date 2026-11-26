"""Prepare proof modules from pjscruggs's published LRAT. Packing and liveness
logic below adapt the pinned project's notes/data/lrat-link/genrow.py.
Generated values are untrusted until checked by the Lean kernel.
"""
from pathlib import Path
from collections import Counter
import gzip

root = Path(__file__).resolve().parent
cnf = root / 'obstruction.cnf'
lrat = root / 'checkout/notes/star-intersection-atlas/obstruction.lrat.gz'
outdir = root / 'checkout/lean/PEqualNP/Quadrangle'
flags = {'--trim'}
seg = 24000
chunk = 350
def lit(x):
    x = int(x)
    return 2 * x if x > 0 else 2 * (-x) + 1


clauses = []
with open(cnf) as fh:
    for line in fh:
        t = line.split()
        if not t or t[0] in ('c', 'p'):
            continue
        assert t[-1] == '0'
        clauses.append([lit(x) for x in t[:-1]])
m = len(clauses)

steps = []  # (id, lits, hints)
with gzip.open(lrat, 'rt', encoding='ascii') as fh:
    for line in fh:
        t = line.split()
        if not t or t[1] == 'd':
            continue
        i = int(t[0])
        z = t.index('0', 1)
        hints = [int(h) for h in t[z + 1:-1]]
        assert all(h > 0 for h in hints), 'RAT hint: not supported'
        steps.append((i, [lit(x) for x in t[1:z]], hints))
        if z == 1:
            break
assert not steps[-1][1], 'no empty clause'

if '--trim' in flags:
    adds = {s[0]: s for s in steps}
    need = {steps[-1][0]}
    stack = [steps[-1][0]]
    while stack:
        for h in adds[stack.pop()][2]:
            if h > m and h not in need:
                need.add(h)
                stack.append(h)
    steps = [s for s in steps if s[0] in need]

# Unit literal after each hint (the checker cannot afford Nat.log2); cut at the first conflict.
neg = lambda l: l ^ 1
cl = {i + 1: c for i, c in enumerate(clauses)}
new = []
for i, lits, hints in steps:
    F = set(lits)
    hout = []
    ok = False
    for h in hints:
        U = set(cl[h]) - F
        if not U:
            hout.append(h)
            ok = True
            break
        assert len(U) == 1, f'hint {h} of step {i} leaves {len(U)} literals'
        u = next(iter(U))
        hout += [h, u]
        F.add(neg(u))
    assert ok, f'step {i}: no conflict'
    cl[i] = lits
    new.append((i, lits, hout))
steps = new

uses = Counter(h for _, _, hs in steps for h in hs[0::2])
if '--rank' in flags:  # keys by use rank
    key = {h: r for r, (h, _) in enumerate(uses.most_common())}
else:  # keys in creation order (used formula clauses first): insertions walk one edge of the trie
    key = {}
    for h in sorted(h for h in uses if h <= m):
        key[h] = len(key)
    for i, _, _ in steps:
        key[i] = len(key)
nxt = len(key)
for i, _, _ in steps:
    if i not in key:  # never used (the empty clause)
        key[i] = nxt
        nxt += 1
fk = [key[i + 1] + 1 if i + 1 in key else 0 for i in range(m)]


def steptoks(s):
    i, lits, hs = s
    return [key[i]] + lits + [0] + [key[x] if j % 2 == 0 else x for j, x in enumerate(hs)]


# segments
segs = [[]]
cnt = 0
for s in steps:
    segs[-1].append(s)
    cnt += (len(s[2]) + 1) // 2
    if seg and cnt >= seg:
        segs.append([])
        cnt = 0
if not segs[-1]:
    segs.pop()
last = {}
for j, s in enumerate(steps):
    for h in s[2][0::2]:
        last[h] = j
created = {s[0]: j for j, s in enumerate(steps)}
# live clauses at each cut: formula or created before the cut, last used at or after it
bounds = []
j0 = 0
for sg in segs[:-1]:
    j0 += len(sg)
    live = [h for h, lj in last.items() if lj >= j0 and (h <= m or created[h] < j0)]
    bounds.append(sorted(live, key=lambda h: key[h]))

alltoks = [t for s in steps for t in steptoks(s)]
ftoks = [x for c in clauses for x in c + [0]]
btoks = [[x for h in b for x in [key[h] + 1] + cl[h] + [0]] for b in bounds]
W = max([max(alltoks), max(ftoks), max(fk)] + [max(b) for b in btoks if b]).bit_length()
K = 1024 // W


def pack(ts):
    words = []
    for k in range(0, len(ts), K):
        w = 1
        for t in reversed(ts[k:k + K]):
            w = (w << W) | t
        words.append(w)
    return words


def L(xs):
    return '[' + ','.join(map(str, xs)) + ']'


def wordsdef(o, nm, ws):
    parts = []
    for k in range(0, len(ws), chunk):
        o.write(f'def {nm}_{k // chunk} : List Nat := [\n' + ',\n'.join(map(str, ws[k:k + chunk])) + ']\n\n')
        parts.append(f'{nm}_{k // chunk}')
    o.write(f'def {nm} : List Nat := ' + (' ++ '.join(parts) or '[]') + '\n\n')


def block(name, imports, body):
    module = outdir / (name + '.lean')
    preface = ''.join('import ' + imp + '\n' for imp in imports)
    module.write_text(preface + '\nnamespace PEqualNP.Quadrangle.Certificate\nopen PEqualNP.Library.LRAT\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n' + body + '\nend PEqualNP.Quadrangle.Certificate\n')

from io import StringIO
def packed(nm, data):
    out = StringIO()
    wordsdef(out, nm, pack(data))
    return out.getvalue()

ns = 'PEqualNP.Quadrangle.'
blocks = [clauses[i:i+45] for i in range(0,m,45)]
f = '\n'.join('def cnf' + str(i) + ' : List (List Nat) := [' + ','.join(L(c) for c in block_) + ']' for i,block_ in enumerate(blocks))
f += '\ndef formula : List (List Nat) := [' + ','.join('cnf'+str(i) for i in range(len(blocks))) + '].flatten\n'
block('Formula', ['PEqualNP.Library.LRAT.Checker'], f)
block('Keys',[ns+'Formula'],packed('keysPacked',fk) + f'noncomputable def keys := unpack {W} keysPacked\n')
for k, data in enumerate(btoks, 1):
    nm = 'boundary'+str(k)
    block('Boundary'+str(k), ['PEqualNP.Library.LRAT.Checker'], packed(nm+'w',data) + f'noncomputable def {nm} := decodeF (unpack {W} {nm}w)\n')
for k, sg in enumerate(segs):
    deps = []
    if k == 0:
        deps = ['Keys', 'Boundary1']
        typ = '∀ a, (∀ c ∈ formula, ClauseSat a c) → EntriesSat a boundary1'
        proof = f'checkFirst_sound formula keys {W} proof{k} boundary1'
    elif k == len(segs)-1:
        deps = ['Boundary'+str(k)]
        typ = f'∀ a, EntriesSat a boundary{k} → False'
        proof = f'checkLast_sound boundary{k} {W} proof{k}'
    else:
        deps = ['Boundary'+str(k),'Boundary'+str(k+1)]
        typ = f'∀ a, EntriesSat a boundary{k} → EntriesSat a boundary{k+1}'
        proof = f'checkSeg_sound boundary{k} {W} proof{k} boundary{k+1}'
    block('Part'+str(k),[ns+x for x in deps],packed('proof'+str(k),[t for s in sg for t in steptoks(s)])+f'theorem part{k} : {typ} :=\n  {proof} (by decide +kernel)\n')
expr = 'part0 a ha'
for k in range(1,len(segs)):
    expr = f'part{k} a ({expr})'
block('Certificate',[ns+'Part'+str(k) for k in range(len(segs))], f'theorem unsat : ¬ FormulaSat formula := fun ⟨a, ha⟩ =>\n  {expr}\n')
print(f'{len(clauses)} clauses, {len(steps)} retained additions, {len(segs)} segments; token field width {W}',flush=True)

