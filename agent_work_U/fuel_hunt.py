"""Scenario-A hunt with fuel Z != S: for W over gadget trees (<= n letters) and Z over small closed terms, walk W.Z and
record walks that run >= NODES nodes while the stack never pops below Z (Z frozen).  Report classes (L36 flag)."""
import sys, time
from dm import *
from classes import cls, LFl, MFl, clear_cache
from collections import Counter
NODES = 300
ALPHA = ["S", "SS", "SSS", "S(SS)", "S(SS)(SS)", "S(S(SS))(S(SS))", "SS(SS)", "S(SSS)"]
alpha = [parse(v) for v in ALPHA]
def trees(n):
    if n == 1:
        for a in alpha: yield a
        return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def rdepth(u):
    d = 0
    while u != 0: u = R[u]; d += 1
    return d
def walk(u, Z):
    dz = rdepth(Z)
    for j in range(NODES):
        if u == 0: return "S", j
        if rdepth(u) <= dz: return "popped", j
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: return "jump", j
        st = list(reversed(spine(u)[0])); k = 0; bud = max(3000, 20 * size(u))
        while len(st) > 2:
            x = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
            if k > bud: return "bot?", j
        u = st[-1]
        if size(u) > 100000: return "huge", j
    return "long", NODES
Zs = [parse(z) for z in ["SS", "SSS", "S(SS)", "SS(SS)", "S(SSS)", "S(S(SS))", "SS(SSS)", "S(SS)S", "S(SS)(SS)"]]
stat = Counter(); t0 = time.time()
for n in range(1, int(sys.argv[1]) + 1):
    for W in trees(n):
        for Z in Zs:
            m = mark()
            t = app(W, Z); c = cls(t)
            if MFl[c[1]] == 1:
                w, j = walk(t, Z)
                stat[(w, LFl[c[0]])] += 1
                if w in ("long", "huge"): print("LONG", w, show(t), c, flush=True)
            truncate(m); clear_cache(m)
    print(n, dict(stat), round(time.time() - t0), "s", flush=True)
