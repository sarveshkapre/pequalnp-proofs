"""Compare anonymous-line trees with a labeled-leaf enumeration at smaller budgets."""
from collections import Counter
from itertools import combinations, permutations, product
import sys
from tree import tables, stretch, HERE, SHAPES, row_profiles
from mixing_bound_six import input_tables, make_tree_enumerator


def relabel(table, width, sigma):
    codes = 1 << width
    out = 0
    for new in range(codes):
        old = sum(((new >> j) & 1) << k for j,k in enumerate(sigma))
        for row in range(4):
            out |= ((table >> (row*codes+old))&1) << (row*codes+new)
    return out


def check_small():
    # Four input leaves, then eight independent six/seven-leaf comparisons.
    for masks, width in [((1,2),2), ((1,2,4),3), ((3,5,6),3),
                         ((1,2,4),4), ((3,5,6),4), ((0,1,2,4),3),
                         ((1,1,2,4),3), ((1,2,3,4),3), ((1,2,4,7),3)]:
        inputs=input_tables(masks,width)
        pts=(1<<len(masks))-1
        full=(1<<len(inputs))-1
        oracle=make_tree_enumerator(inputs,pts,full^pts)
        wanted=oracle(full)
        by_order={relabel(t,width,s) for t,s in product(tables(masks,width),permutations(range(width)))}
        assert wanted == by_order, (masks,width,len(wanted),len(by_order))
        print(masks,width,len(wanted),'labeled tables',flush=True)


def check_line_encoding():
    for left,right in product(range(1,4),repeat=2):
        for high in (False,True):
            width = right if high else left
            for row in range(4):
                for word in range(1<<width):
                    flag = 1<<(row*(1<<width)+word)
                    actual = stretch(flag,left,right,high)
                    wanted = sum(1<<(row*(1<<(left+right))+x)
                                 for x in range(1<<(left+right))
                                 if (x>>left if high else x% (1<<left)) == word)
                    assert actual == wanted


def check_physical_controls():
    from pair_prune import layout
    from cases import ROWS, verify
    for active in combinations(range(6), 3):
        fixed, _, _ = layout(active)
        for points in (3,4):
            gates = list(fixed)
            def add(op, a, b):
                result = 30+len(gates)
                gates.append((op,a,b))
                return result
            frozen = [30+j for j,(op,_,_) in enumerate(fixed) if op=='and']
            terms = []
            row_masks = []
            for i,p in enumerate(active):
                members = [6+l for l in range(11) if ROWS[p] >> l & 1]
                sig = members[0]
                for leaf in members[1:]:
                    sig = add('or',sig,leaf)
                outside = next(6+l for l in range(11) if not ROWS[p] >> l & 1)
                extra = add('or',sig,outside) if points == 3 or i != 2 else None
                row_masks.append((sig,extra))
            other_point = add('or',active[0],active[1]) if points==4 else None
            mixed_start = 30+len(gates)
            for i,(p,(r,extra)) in enumerate(zip(active,row_masks)):
                v = add('and',p,r)
                if extra is not None:
                    v = add('and',v,extra)
                if i == 0 and other_point is not None:
                    v = add('and',v,other_point)
                terms.append(v)
            out = add('or',add('or',terms[0],terms[1]),terms[2])
            assert out == mixed_start+7
            reads = Counter(x for _,a,b in gates[mixed_start-30:] for x in (a,b))
            assert all(c==1 for c in reads.values()) and len(reads)==16
            assert len([x for x in reads if x<mixed_start])==9
            point_roles = {p: 1 << i for i,p in enumerate(active)}
            if other_point is not None:
                point_roles[other_point] = 3
            def signature(w):
                if w < mixed_start:
                    return ((point_roles[w],), (), point_roles[w] << 1) if w in point_roles else ((), (w,), 0b10101010)
                op,a,b = gates[w-30]
                left,right = sorted((signature(a),signature(b)), key=lambda t:(t[0],len(t[1])))
                x = stretch(left[2],len(left[1]),len(right[1]),False)
                y = stretch(right[2],len(left[1]),len(right[1]),True)
                return (tuple(sorted(left[0]+right[0])),left[1]+right[1],x & y if op=='and' else x | y)
            masks,line_wires,table = signature(out)
            assert len(masks)==points and table in tables(masks,len(line_wires))
            s = '012' if ROWS[active[0]] & ROWS[active[1]] & ROWS[active[2]] else '013'
            assert row_profiles(table,len(line_wires),SHAPES[s]) is not None
            for w in frozen:
                out = add('or',out,w)
            assert not verify(gates,detail=False)
            print('physical',active,points,'point /',9-points,'line; 8 mixed tree;',
                  len(gates)-15,'block gates; 177 tests passed')


if __name__ == '__main__':
    check_line_encoding()
    check_small()
    sys.path.insert(0,str(HERE.parents[2]))
    check_physical_controls()
