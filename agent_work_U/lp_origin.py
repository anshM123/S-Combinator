"""At each size-large push in a component walk: is the popped multiplier q a subterm of the ORIGINAL term?  Is the stack
v a subterm?  (Compare: in the reload cycle the popped multiplier B N_k is constructed.)"""
import sys
from dm import *
from classes import cls, COMPONENT, MFl
from chainsrc import chain
from collections import Counter
def subterms(t):
    out = set(); st = [t]
    while st:
        x = st.pop()
        if x in out: continue
        out.add(x)
        if x > 0: st.append(L[x]); st.append(R[x])
    return out
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
stat = Counter(); ex = []
for n in range(3, int(sys.argv[1]) + 1):
    for t in trees(n):
        if cls(t) not in COMPONENT: continue
        sub = subterms(t); u = t
        for j in range(200):
            if u == 0: break
            q1, v = L[u], R[u]
            if q1 == 0: u = v; continue
            a = spine(q1)[0]
            if len(a) == 1: u = a[0]; continue
            r = chain(q1, v)
            if r is None: break
            c, pushed = r
            if any(size(q) >= size(q1) for (q, s) in pushed) and MFl[cls(c)[1]] == 1:
                key = (q1 in sub, v in sub)
                stat[key] += 1
                if key[0] is False and len(ex) < 8: ex.append((show(t), show(q1), show(v)))
            u = c
print("(popped q original?, stack v original?):", dict(stat)); print(ex)
