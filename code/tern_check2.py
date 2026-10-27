"""Ruler-law test on gap subsequences of a candidate ternary counter (main agent)."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
from rand_radix import opseq
def vb(n, b):
    c = 0
    while n % b == 0: n //= b; c += 1
    return c
src = sys.argv[1]; STEPS = int(sys.argv[2]); OP = int(sys.argv[3])
seq = opseq(parse(src), STEPS)
pos = [i for i, x in enumerate(seq) if x == OP]
g = [b - a for a, b in zip(pos, pos[1:])]
for base_val in (6, 7):
    sub = [x for x in g if x >= base_val and (x - base_val) % 3 == 0 and x not in (8,)]
    best = None
    for skip in (0, 5, 20, 100):
        tail = sub[skip:]
        for off in range(0, 3 ** 6):
            mism = sum(1 for j, x in enumerate(tail) if x != base_val + 3 * vb(j + 1 + off, 3))
            if best is None or mism < best[0]: best = (mism, skip, off, len(tail))
            if mism == 0: break
        if best[0] == 0: break
    print(f"family {base_val}+3j: {len(sub)} gaps; best fit sub[{best[1]}:] = {base_val} + 3*v3(j+1+{best[2]}): "
          f"{best[0]} mismatches of {best[3]}; first 40: {sub[:40]}")
