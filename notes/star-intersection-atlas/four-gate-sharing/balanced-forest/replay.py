"""Rebuild rectangle covers from first principles and test the full bipartite grid."""
from collections import defaultdict, deque
from itertools import combinations
from math import comb
from random import Random


def components(vertices, adj):
    todo = set(vertices)
    out = []
    while todo:
        seed = min(todo)
        todo.remove(seed)
        seen, queue = {seed}, [seed]
        for v in queue:
            add = adj[v] & todo
            seen.update(add)
            todo.difference_update(add)
            queue.extend(sorted(add))
        out.append(seen)
    return out


def forest_homes(adj):
    # Choose a centroid, projecting it onto the path between two boundary
    # attachments when needed. Encode child choices as weighted prefix words.
    home = {}

    def place(groups, path):
        if not groups:
            return
        total = sum(map(len, groups))
        lengths = [(max(1, ((total-1)//len(g)).bit_length()), min(g), g) for g in groups]
        code = width = 0
        for size, _, group in sorted(lengths):
            code <<= size-width
            assert code < 1 << size
            split(group, path + format(code, '0%db' % size))
            code += 1
            width = size

    def split(part, path):
        start = min(part)
        parent, order = {start: None}, [start]
        for v in order:
            for w in sorted(adj[v] & part):
                if w != parent[v]:
                    assert w not in parent
                    parent[w] = v
                    order.append(w)
        weight = dict.fromkeys(part, 1)
        for v in reversed(order[1:]):
            weight[parent[v]] += weight[v]
        centroid = next(v for v in order if 2*max(
            [len(part)-weight[v]] + [weight[w] for w in adj[v] & part if parent[w] == v]
        ) <= len(part))
        contacts = [v for v in part for _ in adj[v]-part]
        assert len(contacts) <= 2
        cut = centroid
        if len(contacts) == 2:
            def ancestors(v):
                route = []
                while v is not None:
                    route.append(v)
                    v = parent[v]
                return route
            a, b = map(ancestors, contacts)
            common = next(v for v in a if v in b)
            corridor = set(a[:a.index(common)+1] + b[:b.index(common)])
            dist, queue = {centroid: 0}, deque([centroid])
            while queue:
                cut = queue.popleft()
                if cut in corridor:
                    break
                for w in sorted((adj[cut] & part)-dist.keys()):
                    dist[w] = dist[cut]+1
                    queue.append(w)
        home[cut] = path
        groups = components(part-{cut}, adj)
        for g in groups:
            if 2*len(g) > len(part):
                assert sum(len(adj[v]-g) for v in g) == 1
        place(groups, path)

    groups = components(range(len(adj)), adj)
    if len(groups) == 1:
        split(groups[0], '')
    else:
        place(groups, '')
    return home


def rank_word(rank, bits):
    """Lexicographically unrank on the middle layer, without enumerating it."""
    need = bits//2
    out = ''
    for left in reversed(range(bits)):
        count_zero = comb(left, need) if need <= left else 0
        if rank < count_zero:
            out += '0'
        else:
            rank -= count_zero
            need -= 1
            out += '1'
    assert rank == need == 0
    return out


def width(count):
    w = 0
    while comb(w, w//2) < count:
        w += 1
    return w


def cover(adj, left, home, block, max_reads):
    right = sorted(set(range(len(adj)))-set(left))
    group = {v: path[:len(path)//block*block] for v,path in home.items()}
    weight = defaultdict(int)
    siblings = defaultdict(set)
    for g in group.values():
        for end in range(0, len(g)+1, block):
            weight[g[:end]] += 1
            if end:
                siblings[g[:end-block]].add(g[:end])
    words = {'': ''}
    header = width((len(adj)-1).bit_length()+1)
    for parent in sorted(siblings, key=len):
        classes = defaultdict(list)
        for g in sorted(siblings[parent]):
            s = ((weight[parent]-1)//weight[g]).bit_length()
            classes[s].append(g)
        for s, gs in classes.items():
            assert len(gs) <= 2**s
            for rank, g in enumerate(gs):
                words[g] = words[parent] + rank_word(s, header) + rank_word(rank,width(2**s))
    size = max(map(len, words.values()))
    rowbits = {v:int(words[g].ljust(size,'0') or '0',2) for v,g in group.items()}
    colbits = {v:int(words[g].ljust(size,'1') or '0',2) for v,g in group.items()}
    local = defaultdict(list)
    for v,g in group.items():
        local[g].append(v)
    tag = {v:(len(g)//block, slot) for g,vs in local.items() for slot,v in enumerate(sorted(vs))}
    tags = sorted(set(tag.values()))
    earlier = {v:{w for w in adj[v] if (len(home[w]), w) < (len(home[v]), v)} for v in home}
    assert all(len(ns) <= max_reads for ns in earlier.values())
    for v,ns in earlier.items():
        assert all(home[v].startswith(home[w]) for w in ns)
    dictionary = {v:{tag[w] for w in ns} for v,ns in earlier.items()}
    # Deterministically seeded search for palettes. Stop when each requested
    # tag nonmembership in both directions has a witness. This test uses only
    # tag dictionaries; it never consults the target adjacency matrix.
    cells = [(x,y) for x in left for y in right]
    todo = {(tag[x],frozenset(dictionary[x]),tag[y],frozenset(dictionary[y]))
            for x,y in cells if tag[x] not in dictionary[y] and tag[y] not in dictionary[x]}
    palettes = []
    rng = Random(717)
    for _ in range(30000):
        if not todo:
            break
        red,blue = [{t for t in tags if rng.randrange(max_reads+1)==0} for _ in range(2)]
        hits = {k for k in todo if k[0] in red and k[2] in blue and not (k[3]&red or k[1]&blue)}
        if hits:
            palettes.append((red,blue))
            todo -= hits
    assert not todo
    lm = {x:sum(1<<i for i,(r,b) in enumerate(palettes)
                if tag[x] in r and not dictionary[x]&b) for x in left}
    rm = {y:sum(1<<i for i,(r,b) in enumerate(palettes)
                if tag[y] in b and not dictionary[y]&r) for y in right}
    omit_branch = omit_tags = 0
    for x,y in cells:
        compatible = not (rowbits[x] & ~colbits[y])
        assert compatible == (group[x].startswith(group[y]) or group[y].startswith(group[x]))
        tag_hit = not (lm[x] & rm[y])
        assert tag_hit == (tag[x] in dictionary[y] or tag[y] in dictionary[x])
        assert (compatible and tag_hit) == (y in adj[x])
        omit_branch += tag_hit and not compatible
        omit_tags += compatible and not tag_hit
    return len(cells), omit_branch, omit_tags


def graph(n, edges):
    adj = [set() for _ in range(n)]
    for u,v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def shores(adj):
    colors = {}
    for v in range(len(adj)):
        if v in colors:
            continue
        colors[v] = 0
        queue = [v]
        for x in queue:
            for y in adj[x]:
                if y not in colors:
                    colors[y] = 1-colors[x]
                    queue.append(y)
                assert colors[y] != colors[x]
    return sorted(x for x,c in colors.items() if c == 0)


def reduction_checks():
    edges = [(x,y) for x in range(3) for y in range(3,7)]
    restored = 0
    for mask in range(1 << len(edges)):
        adj = graph(7,[edge for i,edge in enumerate(edges) if mask>>i & 1])
        representative = {}
        first = {}
        for v,neighbors in enumerate(adj):
            if neighbors:
                representative[v] = first.setdefault(frozenset(neighbors),v)
        vs = set(first.values())
        nbr = {v:adj[v] & vs for v in vs}
        assert len({frozenset(s) for s in nbr.values()}) == len(vs)
        for x,y in edges:
            lifted = x in representative and y in representative and representative[y] in nbr[representative[x]]
            assert lifted == (y in adj[x])
            restored += 1
        cover_set = next(set(ss) for k in range(len(vs)+1) for ss in combinations(sorted(vs),k)
                         if all(v in ss or w in ss for v in vs for w in nbr[v]))
        # Fill the remaining neighbors into a clique at each elimination. Check
        # every vertex charge rather than only the final, looser order bound.
        rem, fill = set(vs), {v:set(s) for v,s in nbr.items()}
        later, order = {}, {}
        while rem:
            v = min(rem,key=lambda u:(len(fill[u]&rem),u))
            rem.remove(v)
            order[v] = len(order)
            later[v] = fill[v]&rem
            for a,b in combinations(later[v],2):
                fill[a].add(b)
                fill[b].add(a)
        w = max(map(len,later.values()),default=0)
        charged = defaultdict(set)
        signatures = defaultdict(set)
        for v in vs-cover_set:
            x = min(nbr[v],key=order.get)
            if order[x] < order[v]:
                assert v in later[x]
                charged[x].add(v)
            else:
                key = frozenset(nbr[v]-{x})
                assert key <= later[x] and key not in signatures[x]
                signatures[x].add(key)
        assert all(len(charged[x]) <= w and len(signatures[x]) <= 2**w for x in cover_set)
        assert len(vs) <= (1+w+2**w)*len(cover_set)
    print(f'Twin reduction and vertex-cover accounting: 4096 graphs; {restored} restored cells.')


def main():
    results = defaultdict(list)
    raw = [(i,3+j) for i in range(3) for j in range(3)]
    for mask in range(512):
        adj = graph(6,[e for i,e in enumerate(raw) if mask>>i & 1])
        if mask.bit_count() != 6-len(components(range(6),adj)):
            continue
        home = forest_homes(adj)
        for b in (1,2,3):
            results['all 3x3 forests'].append(cover(adj,range(3),home,b,2))
    for name,n,edges in [
        ('path',159,[(i,i+1) for i in range(158)]),
        ('subdivided star',145,[(0,i) for i in range(1,73)]+[(i,i+72) for i in range(1,73)]),
        ('branching tree',192,[((i-1)//(2 if i<36 else 7),i) for i in range(1,192)]),
        ('binary tree',127,[((i-1)//2,i) for i in range(1,127)]),
    ]:
        adj = graph(n,edges)
        home = forest_homes(adj)
        for b in (1,3,5):
            results[name].append(cover(adj,shores(adj),home,b,2))
    # Cyclic, high-degree graph of treewidth two. The two hubs share a home
    # and distinct slots. Every other vertex records them both.
    adj = graph(82,[(i,j) for i in range(2) for j in range(2,82)])
    home = {0:'',1:'',**{j:format(j-2,'07b') for j in range(2,82)}}
    results['two hubs and 80 common neighbors'].append(cover(adj,[0,1],home,2,2))
    # Two rows per rung in the balanced path decomposition of a ladder.
    n = 68
    adj = graph(2*n,[(2*i,2*i+1) for i in range(n)]+
                [(2*i+k,2*i+2+k) for i in range(n-1) for k in range(2)])
    home = {}
    def midpoint(lo,hi,path):
        if lo>=hi:
            return
        m = (lo+hi)//2
        home[2*m] = home[2*m+1] = path
        midpoint(lo,m,path+'0')
        midpoint(m+1,hi,path+'1')
    midpoint(0,n,'')
    for b in (1,2,4):
        results['ladder'].append(cover(adj,shores(adj),home,b,3))
    total = [0,0,0]
    for name,rows in results.items():
        counts = list(map(sum,zip(*rows)))
        print(f'{name}: {len(rows)} covers, {counts[0]} cells')
        total = [a+b for a,b in zip(total,counts)]
    assert min(total[1:]) > 0
    print(f'Total: {total[0]} exact cell checks. False positives without branch tests: {total[1]}; without tag tests: {total[2]}.')
    reduction_checks()


if __name__ == '__main__':
    main()
