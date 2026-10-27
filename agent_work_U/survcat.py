"""Catalogue of FIRST-ROUND survivors: for closed C <= NMAX leaves, run the DM on the list ch(C) ++ [x1..xK]
(i.e. the state C x1 .. xK) until the first descent ([c,d] -> c).  Record the survivor c if it is CODE-headed
(S-headed) and contains every atom (data preserved).  Print distinct survivor shapes (closed subterms abbreviated
by size) with the smallest C.  usage: python survcat.py NMAX K BUDGET"""
import sys
from dm import *
NMAX, K, BUDGET = map(int, sys.argv[1:4])
xs = [atom("x%d" % (i + 1)) for i in range(K)]
def has(i, a):
    st = [i]
    while st:
        j = st.pop()
        if j == a: return True
        if j > 0: st.append(L[j]); st.append(R[j])
    return False
def closed(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True
def skel(i):
    """shape: closed maximal subterms -> 'c<size>'"""
    if i < 0: return NAMES[i]
    if closed(i): return "#" if i == 0 else "c%d" % size(i)
    args, h = spine(i)
    s = skel(h) if h != 0 else "S"
    return s + "".join("(" + skel(a) + ")" for a in args)
res = {}
for n in range(1, NMAX + 1):
    for C in trees(n):
        args, h = spine(C)
        st = list(reversed(args + xs))
        surv = None
        for t in range(BUDGET):
            m = len(st)
            if m >= 3:
                a = st[-1]; aa, ah = spine(a)
                if ah != 0: break
                st.pop(); b = st.pop(); c = st.pop()
                st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
            else:
                if m >= 1: surv = st[-1]
                break
        if surv is None: continue
        if head(surv) != 0: continue
        if not any(has(surv, a) for a in xs): continue
        key = skel(surv)
        if key not in res: res[key] = (n, show(C), show(surv, maxlen=120))
for k, v in sorted(res.items(), key=lambda kv: (len(kv[0]), kv[0])):
    print("%-50s <= %s  [%s]" % (k, v[1], v[2]))
print("distinct", len(res))
