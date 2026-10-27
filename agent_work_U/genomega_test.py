"""Generalized Omega test.  If the R2-chain of X (H(X) = S (SS) X1, H(X1) = S (SS) X2, ...) reaches a term Y with head
normal form exactly S (S(SS)) (S(SS)), then the leftmost walk of M.X (M = S(S(SS))(S(SS))) is infinite:
M.X -> X.(S(SS).X) -> (R2 count-down of the top) -> Y.(S(SS).X) -> (S(SS).X).(S(SS).(S(SS).X)) -> ...  .
L36 must give every such M.X flag 1 (class 8 . [X] in {9}).  Enumerate X <= n leaves; also walk M.X to confirm."""
import sys, time
from dm import *
from classes import cls, LFl, MFl, clear_cache
from collections import Counter
SS = app(0, 0); SSS_ = app(0, SS)          # S(SS)
M = parse("S(S(SS))(S(SS))")
def H(u, bud=20000):
    a = spine(u)[0]
    if len(a) <= 2: return a
    st = list(reversed(a)); k = 0
    while len(st) > 2:
        x = st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
        if k > bud: return None
    return list(reversed(st))
def reaches_Mhnf(X, maxlen=200):
    for i in range(maxlen):
        h = H(X)
        if h is None or len(h) != 2: return False
        if h[0] == SSS_ and h[1] == SSS_: return True
        if h[0] != SS: return False
        X = h[1]
    return False
def walk(u, nodes=300):
    for j in range(nodes):
        if u == 0: return "S"
        a = spine(u)[0]
        if len(a) <= 2: u = a[0]; continue
        h = H(u, bud=max(5000, 20 * size(u)))
        if h is None: return "bot?"
        u = h[0]
    return "long"
stat = Counter(); bad = []; t0 = time.time()
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
for n in range(1, int(sys.argv[1]) + 1):
    for X in trees(n):
        m = mark()
        if reaches_Mhnf(X):
            t = app(M, X); c = cls(t)
            w = walk(t)
            stat[(n, c, w)] += 1
            if LFl[c[0]] == 0: bad.append((show(X), c, w))
        truncate(m); clear_cache(m)
    print(n, {k: v for k, v in stat.items() if k[0] == n}, round(time.time() - t0), "s", flush=True)
print("FLAG-0 generalized Omega terms (would contradict L36):", bad[:20])
