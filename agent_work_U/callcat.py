"""Calls with a tape: closed C, data x, y, tape r.  Run from ch(C) ++ [x, y, r] until the first atom-headed front
(no descent: the list never shrinks to 2 because r is below).  Record the stuck list as a skeleton: the first few
list elements (front first) with closed parts abbreviated.  usage: python callcat.py NMAX BUDGET"""
import sys, collections
from dm import *
NMAX, BUD = map(int, sys.argv[1:3])
X, Y, Rr = atom("x"), atom("y"), atom("r")
NM = {X: "x", Y: "y", Rr: "r"}
def closed(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True
def skel(i):
    if i in NM: return NM[i]
    if closed(i): return "c"
    args, h = spine(i)
    s = NM.get(h, "S")
    return s + "".join("(" + skel(a) + ")" for a in args)
cnt = collections.Counter(); ex = {}
for n in range(1, NMAX + 1):
    for C in trees(n):
        args, h = spine(C)
        st = list(reversed(args + [X, Y, Rr]))
        hit = None
        for t in range(BUD):
            if len(st) < 3: break
            a = st[-1]; aa, ah = spine(a)
            if ah != 0:
                hit = list(reversed(st)); break
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
        if hit is None: continue
        # list front first; drop the tape element r if it is last and untouched
        key = " | ".join(skel(e) for e in hit)
        cnt[key] += 1
        if key not in ex: ex[key] = show(C)
items = sorted(cnt.items(), key=lambda kv: (len(kv[0]), kv[0]))
for key, v in items[:45]:
    print("%-70s %5d  e.g. %s" % (key, v, ex[key]))
print("distinct", len(cnt))
