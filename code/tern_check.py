"""Check a candidate ternary counter: gaps of opcode OP against lo + step*v3(k + off) (main agent)."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
from rand_radix import opseq
def vb(n, b):
    c = 0
    while n % b == 0: n //= b; c += 1
    return c
src = sys.argv[1]; STEPS = int(sys.argv[2]); OP = int(sys.argv[3]); B = int(sys.argv[4]) if len(sys.argv) > 4 else 3
seq = opseq(parse(src), STEPS)
print("hnf reached" if seq is None else f"{len(seq)} steps run")
pos = [i for i, x in enumerate(seq) if x == OP]
g = [b - a for a, b in zip(pos, pos[1:])]
cnt = collections.Counter(g)
print("gap value counts:", sorted(cnt.items())[:14])
print("first 60 gaps:", g[:60])
best = None
for skip in (0, 10, 50, 200):
    tail = g[skip:]
    for lo in sorted(cnt)[:3]:
        for step in range(1, 13):
            for off in range(0, 3 ** 5):
                mism = sum(1 for j, x in enumerate(tail) if x != lo + step * vb(j + 1 + off, B))
                if best is None or mism < best[0]: best = (mism, skip, lo, step, off, len(tail))
                if mism == 0: break
            if best and best[0] == 0: break
        if best and best[0] == 0: break
    if best and best[0] == 0: break
print(f"best fit: gaps[{best[1]}:] = {best[2]} + {best[3]}*v{B}(j + 1 + {best[4]}) with {best[0]} mismatches of {best[5]}")
