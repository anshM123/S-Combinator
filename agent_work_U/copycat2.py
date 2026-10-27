"""Two-datum DM rounds: for closed C <= NMAX leaves, run from ch(C) ++ [x, y] until the first descent (stop at an
atom-headed front = data execution).  Record the skeleton of the survivor when it contains data."""
import sys, collections
from dm import *
NMAX, BUD = map(int, sys.argv[1:3])
X, Y = atom("x"), atom("y")
def closed(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True
def skel(i):
    if i == X: return "x"
    if i == Y: return "y"
    if closed(i): return "c"
    args, h = spine(i)
    s = {X: "x", Y: "y"}.get(h, "S")
    return s + "".join("(" + skel(a) + ")" for a in args)
cnt = collections.Counter(); ex = {}
for n in range(1, NMAX + 1):
    for C in trees(n):
        args, h = spine(C)
        st = list(reversed(args + [X, Y]))
        surv = None
        for t in range(BUD):
            m_ = len(st)
            if m_ >= 3:
                a = st[-1]; aa, ah = spine(a)
                if ah != 0: break
                st.pop(); b = st.pop(); c = st.pop()
                st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
            else:
                if m_ >= 1: surv = st[-1]
                break
        if surv is None or closed(surv): continue
        key = skel(surv)
        cnt[key] += 1
        if key not in ex: ex[key] = show(C)
for key, v in sorted(cnt.items(), key=lambda kv: (len(kv[0]), kv[0]))[:40]:
    print("%-70s" % key, v, "e.g.", ex[key])
print("distinct", len(cnt))
