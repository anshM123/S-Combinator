"""Instrumented tail chain (Theorem Q10's chain): node u = q1.v with q1 having >= 2 spine args.
H(q1) = S p0 q0 ('syn' if q1 has exactly 2 args, else 'cmp'); state (p, q, w): p = S final (child w);
p = S x peel -> (x, w, q w) [pushes q; next q is the stack w]; p with >= 2 args refill -> H(p w) = S p' q' -> (p', q', q w).
Each pushed multiplier q_i is tagged by its source: 'syn'/'cmp' (q0 from H(q1)), 'peel' (= a stack), 'refill'."""
import sys
from dm import *
from classes import cls, COMPONENT, MFl
from collections import Counter
def H(u, bud=100000):
    args = spine(u)[0]
    st = list(reversed(args)); k = 0
    while len(st) > 2:
        a = st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c); st.extend(reversed(spine(a)[0])); k += 1
        if k > bud: return None
    return list(reversed(st))
def chain(q1, v):
    a = spine(q1)[0]
    if len(a) == 2: p, q, src = a[0], a[1], "syn"
    else:
        h = H(q1)
        if h is None: return None
        p, q, src = h[0], h[1], "cmp"
    w = v; pushed = []
    for it in range(1000):
        if p == 0: return w, pushed
        pa = spine(p)[0]
        pushed.append((q, src))
        if len(pa) == 1: p, q, w, src = pa[0], w, app(q, w), "peel"
        else:
            h = H(app(p, w))
            if h is None: return None
            p, q, w, src = h[0], h[1], app(q, w), "refill"
    return None
def walk_events(t, maxn=200):
    u = t; ev = []
    for j in range(maxn):
        if u == 0: return ev, "leaf"
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; continue
        r = chain(q1, v)
        if r is None: return ev, "bot"
        c, pushed = r
        big = [(src, size(q), cls(q)) for (q, src) in pushed if size(q) >= size(q1)]
        if big and MFl[cls(c)[1]] == 1: ev.append((cls(u), size(q1), cls(q1), cls(v), len(pushed), big))
        u = c
    return ev, "long"
if __name__ == "__main__":
    def trees(n):
        if n == 1: yield 0; return
        for k in range(1, n):
            for l in trees(k):
                for r in trees(n - k): yield app(l, r)
    srcs = Counter(); ex = {}
    for n in range(3, int(sys.argv[1]) + 1):
        for t in trees(n):
            if cls(t) not in COMPONENT: continue
            ev, end = walk_events(t)
            for e in ev:
                for b in e[5]:
                    key = (b[0], end); srcs[key] += 1
                    if key not in ex: ex[key] = (show(t), e)
    print(srcs)
    for k, v in ex.items(): print(k, v)
