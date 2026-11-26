"""Exhaust the small shared circuits for the live-guard deletion lemma."""
from itertools import combinations_with_replacement, product


def verify():
    inputs = [sum(1 << m for m in range(16) if m >> i & 1) for i in range(4)]
    tested = mixed = 0
    choices = [[(op,a,b) for op in (0,1) for a,b in combinations_with_replacement(range(n),2)]
               for n in (4,5,6)]
    for net in product(*choices):
        live = {6}
        for i in (2,1,0):
            if 4+i in live:
                live.update(net[i][1:])
        used = sum(1 << i for i in range(4) if i in live)
        for frozen in range(1,16):
            if frozen & ~used:
                continue
            cols = [0 if frozen >> i & 1 else x for i,x in enumerate(inputs)]
            old = cols.copy()
            pure = [bool(frozen >> i & 1) for i in range(4)]
            removed = 0
            for j,(op,a,b) in enumerate(net,4):
                old.append((old[a]&old[b]) if op else (old[a]|old[b]))
                pure.append(pure[a] and pure[b])
                if pure[a] or pure[b]:
                    v = 0 if op else (cols[b] if pure[a] else cols[a])
                    removed += int(j in live)
                else:
                    v = (cols[a]&cols[b]) if op else (cols[a]|cols[b])
                cols.append(v)
            assert cols[-1]==old[-1]
            if not pure[-1]:
                assert removed >= frozen.bit_count()
                tested+=1
                mixed+=int(any(op and j in live and (pure[a] or pure[b]) for j,(op,a,b) in enumerate(net,4)))
    print(f"{tested} live-circuit and frozen-input choices, including {mixed} with an AND reading a frozen wire.")


if __name__=="__main__":
    verify()
