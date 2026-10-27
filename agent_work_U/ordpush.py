"""Ordinal version of the large-push measure: o(S) = 0, o(q.v) = omega^o(q) (+) o(v) (natural sum), i.e. the
nested-multiset measure of the right-spine decomposition.  A walk step replaces omega^o(q1) by the omega^o(q_i) of the
pushed multipliers; it is 'o-large' if some o(q_i) >= o(q1).  Count o-large pushes in component walks."""
import sys
from dm import *
from classes import cls, COMPONENT, MFl
from chainsrc import chain
from collections import Counter
sys.setrecursionlimit(100000)
_o = {0: ()}
def o(u):
    r = _o.get(u)
    if r is not None: return r
    st = [u]
    while st:
        x = st[-1]
        if x in _o: st.pop(); continue
        pend = [y for y in (L[x], R[x]) if y not in _o]
        if pend: st.extend(pend); continue
        _o[x] = tuple(sorted((_o[L[x]],) + _o[R[x]], reverse=True)); st.pop()
    return _o[u]
def walk_o(t, maxn=200):
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
        big = [(src, size(q)) for (q, src) in pushed if o(q) >= o(q1)]
        if big and MFl[cls(c)[1]] == 1: ev.append((cls(u), size(q1), len(pushed), big))
        u = c
    return ev, "long"
if __name__ == "__main__":
    def trees(n):
        if n == 1: yield 0; return
        for k in range(1, n):
            for l in trees(k):
                for r in trees(n - k): yield app(l, r)
    dist = Counter(); srcs = Counter(); ex = []
    for n in range(3, int(sys.argv[1]) + 1):
        for t in trees(n):
            if cls(t) not in COMPONENT: continue
            ev, end = walk_o(t)
            dist[(len(ev), end)] += 1
            for e in ev:
                for b in e[3]: srcs[(b[0], end)] += 1
            if ev and end == "leaf" and len(ex) < 6: ex.append((show(t), ev))
    print(sorted(dist.items())); print(srcs)
    for e in ex: print(e)
    for s in ["S(S(SS))(S(SS))(SS)S", "S(S(SS))(S(SS))(S(S(SS))(S(SS)))"]:
        ev, end = walk_o(parse(s), 40); print(s, end, len(ev), ev[:3])
