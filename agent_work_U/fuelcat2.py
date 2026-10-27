"""For one datum x + fuel f: list the distinct survivors of the form x.c (c closed) and record c relative to f."""
import sys, collections
from dm import *
NMAX = int(sys.argv[1]); FUEL = parse(sys.argv[2]); BUD = int(sys.argv[3])
X = atom("x")
def closed(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True
cs = collections.Counter(); ex = {}
for n in range(1, NMAX + 1):
    for C in trees(n):
        args, h = spine(C)
        st = list(reversed(args + [X, FUEL]))
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
        if surv is None: continue
        sa, sh = spine(surv)
        if sh == X and len(sa) == 1 and closed(sa[0]):
            key = show(sa[0]); cs[key] += 1
            if key not in ex: ex[key] = show(C)
print("fuel", show(FUEL), "survivors x.c with c =")
for k, v in cs.most_common(20): print("  c=%-20s %4d  e.g. C=%s" % (k, v, ex[k]))
