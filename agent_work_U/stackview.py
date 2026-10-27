"""Multiplier-stack view of a leftmost walk: node = q1 (q2 (... (qd S))).  Event per node: pop (q1 = S), jump
(q1 = S p0, child p0), chain k (H(q1) = S p0 q0, tail chain of length k pushes k multipliers; k = 0 is a pop)."""
import sys
from dm import *
from classes import cls
def rspine(u):
    qs = []
    while u != 0:
        qs.append(L[u]); u = R[u]
    return qs
def hnf(u, bud=200000):
    args, h = spine(u)
    st = list(reversed(args)); k = 0
    while len(st) > 2:
        a = st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c); st.extend(reversed(spine(a)[0])); k += 1
        if k > bud: return None
    return list(reversed(st))
def events(s, maxn=60):
    u = parse(s); out = []
    for j in range(maxn):
        if u == 0: out.append("leaf"); break
        q1, v = L[u], R[u]
        d = len(rspine(u))
        if q1 == 0: out.append(("pop", d)); u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: out.append(("jump", d, size(a[0]))); u = a[0]; continue
        H = hnf(u)
        if H is None: out.append("bot"); break
        c = H[0]
        # chain length = number of multipliers pushed over v: c = q_{k-1}(...(q_0 v))
        k = 0; x = c
        while x != v and x != 0:
            x = R[x]; k += 1
        if x != v: k = -1
        out.append(("chain", d, k, size(q1), cls(q1), cls(v)))
        u = c
    return out
if __name__ == "__main__":
    for s in sys.argv[1:]:
        print("==", s, cls(parse(s)))
        for e in events(s): print("   ", e)
