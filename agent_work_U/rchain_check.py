"""Sanity checks for the stripping theorem.  R(P, P') iff H(P) = S S P'.  (1) Exhaustive: for all closed P <= n leaves,
follow the R-chain (deterministic) and record the maximal length; (2) the stripping step: for P with >= 3 args and
R(P, P'), check P = Q.S, R(Q, y) and P' = y.S."""
import sys
from dm import *
from collections import Counter
def H(u, bud=20000):
    st = list(reversed(spine(u)[0])); k = 0
    while len(st) > 2:
        a = st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c); st.extend(reversed(spine(a)[0])); k += 1
        if k > bud: return None
    return list(reversed(st))
def Rsucc(P):
    a = spine(P)[0]
    if len(a) < 2: return None
    h = H(P)
    if h is None or len(h) != 2 or h[0] != 0: return None
    return h[1]
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
mx = Counter(); bad = 0; checked = 0
for n in range(1, int(sys.argv[1]) + 1):
    for P in trees(n):
        # chain length
        k = 0; Q = P
        while k < 1000:
            Q2 = Rsucc(Q)
            if Q2 is None: break
            k += 1; Q = Q2
        mx[(n, k)] += 1
        # stripping step
        P2 = Rsucc(P)
        if P2 is not None and len(spine(P)[0]) >= 3:
            checked += 1
            ok = (R[P] == 0) and (R[P2] == 0) and Rsucc(L[P]) == L[P2]
            if not ok: bad += 1
print("max chain length by size:", {n: max(k for (m, k) in mx if m == n) for n in range(1, int(sys.argv[1]) + 1)})
print("stripping step checked:", checked, "violations:", bad)
