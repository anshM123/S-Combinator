"""Scenario C search: leftmost walks with many jumps among gadget trees (<= n letters, 8 gadget letters)."""
import sys, time
from dm import *
from classes import cls, LFl, MFl, clear_cache
from collections import Counter
ALPHA = ["S", "SS", "SSS", "S(SS)", "S(SS)(SS)", "S(S(SS))(S(SS))", "SS(SS)", "S(SSS)"]
alpha = [parse(v) for v in ALPHA]
def trees(n):
    if n == 1:
        for a in alpha: yield a
        return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def walk(u, nodes=400):
    nj = 0; last = -1
    for j in range(nodes):
        if u == 0: return "S", nj, last
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: nj += 1; last = j; u = a[0]; continue
        st = list(reversed(spine(u)[0])); k = 0; bud = max(3000, 20 * size(u))
        while len(st) > 2:
            x = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
            if k > bud: return "bot?", nj, last
        u = st[-1]
        if size(u) > 100000: return "huge", nj, last
    return "long", nj, last
stat = Counter(); t0 = time.time(); best = []
for n in range(1, int(sys.argv[1]) + 1):
    for t in trees(n):
        m = mark()
        w, nj, last = walk(t)
        stat[(w, min(nj, 9))] += 1
        if nj >= 6 or (w == "long" and last > 0): best.append((nj, w, last, show(t), cls(t)))
        truncate(m); clear_cache(m)
    print(n, sorted(stat.items()), round(time.time() - t0), "s", flush=True)
best.sort(key=lambda x: -x[0])
for b in best[:15]: print(b)
