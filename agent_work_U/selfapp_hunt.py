"""Self-application hunt (beyond the 16-leaf census): for every closed X with n leaves, the terms X X, X X S and
S X X... (shape given by argv) are walked along the leftmost path (<= NODES nodes, per-round budget).  A walk that does not
end within NODES nodes in a flag-0 class is a candidate counterexample to the finite half; a flag-1 term whose walk ends at
S would contradict Proposition Q''."""
import sys, time
from dm import *
from classes import cls, LFl, MFl, clear_cache
from collections import Counter
NODES = 300
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
def walk(u):
    for j in range(NODES):
        if u == 0: return "S", j
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        st = list(reversed(spine(u)[0])); k = 0; bud = max(3000, 20 * size(u))
        while len(st) > 2:
            x = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
            if k > bud: return "bot?", j
        u = st[-1]
        if size(u) > 200000: return "huge", j
    return "long", NODES
shape = sys.argv[2]
def build(X):
    if shape == "XX": return app(X, X)
    if shape == "XXS": return app(app(X, X), 0)
    if shape == "SXX": return app(app(0, X), X)
    if shape == "X(SX)": return app(X, app(0, X))
    if shape == "XSX": return app(app(X, 0), X)
n = int(sys.argv[1]); stat = Counter(); t0 = time.time()
for X in trees(n):
    m = mark()
    t = build(X); c = cls(t)
    if MFl[c[1]] == 0: stat[("noHNF", LFl[c[0]])] += 1
    else:
        w, j = walk(t)
        stat[(w, LFl[c[0]])] += 1
        if (w in ("long", "huge") and LFl[c[0]] == 0) or (w == "S" and LFl[c[0]] == 1):
            print("CANDIDATE", w, j, show(t), c, flush=True)
    truncate(m); clear_cache(m)
print(shape, n, dict(stat), round(time.time() - t0), "s", flush=True)
