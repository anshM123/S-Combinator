"""Scenario A with excursions: q over gadget trees (<= n letters) with an R19 flag-1 class (infinite rightmost path),
fuel S.  Walk q.S (<= 400 nodes); for long walks record whether every step from a depth-1 node was a tail call (pure
reload type) or some returns used excursions (depth went above 1 and came back).  Report L36 flags."""
import sys, time
from dm import *
from classes import cls, LFl, MFl, clear_cache
from scenA_hunt import rcls, RFl, rdepth
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
    exc = 0; maxd = 0
    for j in range(nodes):
        if u == 0: return "S", j, exc, maxd
        d = rdepth(u); maxd = max(maxd, d)
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        st = list(reversed(spine(u)[0])); k = 0; bud = max(3000, 20 * size(u))
        while len(st) > 2:
            x = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
            if k > bud: return "bot?", j, exc, maxd
        c = st[-1]
        if d == 1 and rdepth(c) > 1: exc += 1
        u = c
        if size(u) > 100000: return "huge", j, exc, maxd
    return "long", nodes, exc, maxd
stat = Counter(); t0 = time.time()
for n in range(1, int(sys.argv[1]) + 1):
    for q in trees(n):
        m = mark()
        if RFl[rcls(q)] == 1:
            t = app(q, 0); c = cls(t)
            if MFl[c[1]] == 1:
                w, j, exc, maxd = walk(t)
                stat[(w, LFl[c[0]], exc > 0)] += 1
                if w in ("long", "huge") and (LFl[c[0]] == 0 or exc > 0):
                    print("NOTE", w, LFl[c[0]], "excursions", exc, "maxdepth", maxd, show(t)[:120], flush=True)
        truncate(m); clear_cache(m)
    print(n, dict(stat), round(time.time() - t0), "s", flush=True)
