"""Generalized reload theorem test.  If the R-chain of w (H(w) = S S w1, H(w1) = S S w2, ...) reaches a term whose head
normal form is exactly S(SS)(SS), then w (SS w) S has an infinite leftmost path (PROVED on paper: R-steps count the
prefix down, the B-hnf term restarts with counter SS w).  L36 must give all these terms flag 1.  Enumerate w <= n leaves."""
import sys, time
from dm import *
from classes import cls, LFl, clear_cache
from collections import Counter
SS = app(0, 0)
def H(u, bud=20000):
    a = spine(u)[0]
    if len(a) <= 2: return a
    st = list(reversed(a)); k = 0
    while len(st) > 2:
        x = st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
        if k > bud: return None
    return list(reversed(st))
def reaches_B(w, maxlen=200):
    for i in range(maxlen):
        h = H(w)
        if h is None or len(h) != 2: return False
        if h[0] == SS and h[1] == SS: return True
        if h[0] != 0: return False
        w = h[1]
    return False
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
stat = Counter(); bad = []; t0 = time.time()
for n in range(1, int(sys.argv[1]) + 1):
    for w in trees(n):
        if reaches_B(w):
            t = app(app(w, app(SS, w)), 0)
            c = cls(t)
            stat[(n, c)] += 1
            if LFl[c[0]] == 0 and len(bad) < 20: bad.append((show(w), show(t), c))
    print(n, {k: v for k, v in stat.items() if k[0] == n}, round(time.time() - t0), "s", flush=True)
print("FLAG-0 (would contradict L36):", bad)
