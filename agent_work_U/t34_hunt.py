"""Case (a') probe: leftmost walks that return to depth 1 (nodes q.S) many times; classify each return step by the
first component x0 of H(q): T1 (x0 = S S), T2 (H(x0) = S S y), T3 (x0 = S(SS)), T4 (H(x0) = S x S, H(x) = S S y'),
other.  Report walks with T3/T4 returns after a burn-in (a new depth-1 mechanism would show up here)."""
import sys, random, time
from dm import *
from classes import cls, LFl, clear_cache
from stackview import hnf
from em_hunt import rand_term
from collections import Counter
SS = app(0, 0); S_SS = app(0, SS)
G = ["S", "SS", "S(SS)", "S(SS)(SS)", "S(S(SS))(S(SS))", "SS(S(SS)(SS))", "S(SS)(S(S(SS))(S(SS)))", "SSS", "S(SSS)",
     "S(S(SS))", "SS(SS)"]
def letter():
    if random.random() < 0.7: return parse(random.choice(G))
    return rand_term(random.randint(2, 7))
def tree(n):
    if n == 1: return letter()
    k = random.randint(1, n - 1)
    return app(tree(k), tree(n - k))
def h2(t):
    h = hnf(t, bud=20000)
    return h if (h is not None and len(h) == 2) else None
def rtype(q):
    h = h2(q)
    if h is None: return "nohnf"
    x0 = h[0]
    if x0 == SS: return "T1"
    if x0 == S_SS: return "T3"
    hx = h2(x0)
    if hx is not None and hx[0] == 0: return "T2"
    if hx is not None and hx[1] == 0:
        hxx = h2(hx[0])
        if hxx is not None and hxx[0] == 0: return "T4"
    return "other"
def walk(t, nodes, burn):
    u = t; ty = Counter()
    for j in range(nodes):
        if u == 0: return None
        q1, Z = L[u], R[u]
        if Z == 0 and j >= burn and q1 != 0 and len(spine(q1)[0]) >= 2: ty[rtype(q1)] += 1
        if q1 == 0: u = Z; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        Hn = hnf(u, bud=max(20000, 20 * size(u)))
        if Hn is None: return None
        u = Hn[0]
        if size(u) > 300000: return None
    return ty
seed, N, maxl, nodes, burn = [int(x) for x in sys.argv[1:6]]
random.seed(seed); t0 = time.time(); tot = Counter(); nw = 0; ex = []
for it in range(N):
    m = mark()
    t = app(tree(random.randint(1, maxl)), 0) if random.random() < 0.5 else tree(random.randint(2, maxl))
    ty = walk(t, nodes, burn)
    if ty is not None:
        nw += 1; tot.update(ty)
        if (ty["T3"] or ty["T4"] or ty["other"]) and len(ex) < 8: ex.append((show(t)[:110], dict(ty), LFl[cls(t)[0]]))
    truncate(m); clear_cache(m)
print("seed", seed, "walks completing", nodes, "nodes:", nw, "depth-1 return types after burn-in:", dict(tot), round(time.time() - t0), "s")
print("walks with T3/T4/other depth-1 returns after burn-in (term, counts, L36 flag):", ex)
