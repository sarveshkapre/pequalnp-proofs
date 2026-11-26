"""Enumerate mixed AND/OR trees by subset of point leaves and number of line leaves."""
import argparse
from collections import Counter
from functools import cache
from itertools import product
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'profiles'))
from profiles import SHAPES, point_signatures, row_profiles
from mixing_bound_seven import find_reconstruction


@cache
def stretch(table, left, right, high):
    """Embed one child's line bits into the parent: left uses the low bits."""
    width = right if high else left
    child_count = 1 << width
    mask = (1 << child_count) - 1
    parent_count = 1 << (left + right)
    result = 0
    for row in range(4):
        chunk = table >> (row * child_count) & mask
        if high:
            block = (1 << (1 << left)) - 1
            expanded = sum(block << (i << left) for i in range(child_count) if chunk >> i & 1)
        else:
            expanded = chunk * (((1 << parent_count)-1) // mask)
        result |= expanded << (row * parent_count)
    return result


@cache
def tables(masks, lines):
    """Line labels are assigned in the tree's left-to-right leaf order."""
    if len(masks) + lines == 1:
        return {0b10101010} if lines else {masks[0] << 1}
    if not masks or not lines:
        return set()
    outcomes = set()
    points = len(masks)
    for chosen in range(1 << points):
        first = tuple(m for i,m in enumerate(masks) if chosen >> i & 1)
        second = tuple(m for i,m in enumerate(masks) if not (chosen >> i & 1))
        for left in range(lines + 1):
            right = lines - left
            if not (len(first) + left and len(second) + right):
                continue
            if (first,left) > (second,right):
                continue
            a = {stretch(x,left,right,False) for x in tables(first,left)}
            b = {stretch(y,left,right,True) for y in tables(second,right)}
            for x,y in product(a,b):
                outcomes.update((x & y, x | y))
    return outcomes


def codes_for(data, width, shape):
    domain, rows = data
    return [[j for j in range(1<<width) if domain>>j&1 and
             sum(((row>>j)&1)<<i for i,row in enumerate(rows)) == kind] for kind in SHAPES[shape]]


def run(points, lines, path, reconstruct=True):
    cases = []
    seen = {}
    counts = Counter()
    for masks in point_signatures(points):
        q = max(len(set(masks)-{0,1,2,4}),2 if 7 in masks else 0)
        all_tables = tables(masks,lines)
        counts['tables'] += len(all_tables)
        print(masks, 'tables',len(all_tables),flush=True)
        for shape, required in SHAPES.items():
            profiles = {data for t in all_tables if (data:=row_profiles(t,lines,required)) is not None}
            counts[shape,'profiles'] += len(profiles)
            for data in profiles:
                key = (shape, data)
                if key not in seen or q < seen[key]:
                    seen[key] = q
        tables.cache_clear()
        stretch.cache_clear()
    print('distinct raw profiles',len(seen),flush=True)
    for (shape,data),q in sorted(seen.items()):
        if reconstruct and find_reconstruction(lines,*data,budget=3+q) is not None:
            counts[shape,'rebuilt'] += 1
            continue
        cases.append(dict(shape=shape,boundary=lines,line_gates=5-q,codes=codes_for(data,lines,shape)))
    path.write_text(json.dumps(cases,separators=(',',':'))+'\n')
    print(points,lines,counts,'sent to prefix search:',len(cases),flush=True)


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('points',type=int,choices=(3,4))
    p.add_argument('output',type=Path)
    p.add_argument('--no-reconstruction',action='store_true')
    a=p.parse_args()
    run(a.points,9-a.points,a.output,not a.no_reconstruction)
