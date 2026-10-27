"""Random component terms (n leaves, random binary trees by random splits) -> count o-large pushes along the leftmost
walk (ordinal measure of ordpush.py).  Memory-safe (truncate after each term)."""
import sys, random, time
from dm import *
from classes import cls, COMPONENT, clear_cache
from ordpush import walk_o, _o
from collections import Counter
seed, N, lo, hi = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
random.seed(seed)
def rtree(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return app(rtree(k), rtree(n - k))
dist = Counter(); tried = 0; t0 = time.time(); worst = []
while sum(dist.values()) < N and time.time() - t0 < 3000:
    m = mark()
    t = rtree(random.randint(lo, hi)); tried += 1
    if cls(t) in COMPONENT:
        ev, end = walk_o(t, maxn=300)
        dist[(len(ev), end)] += 1
        if len(ev) >= 2: worst.append((len(ev), end, show(t)))
    for k in [k for k in _o if k >= m]: del _o[k]
    truncate(m); clear_cache(m)
print("tried", tried, "component", sum(dist.values()), sorted(dist.items()), round(time.time() - t0), "s")
for w in sorted(worst)[-6:]: print(w)
