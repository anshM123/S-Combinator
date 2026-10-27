"""Catalogue of multi-copy survivors of single-datum DM rounds: for closed C <= NMAX leaves, run the DM from ch(C) ++ [x]
until the first descent; if the survivor holds x >= 2 times, record its skeleton (maximal closed subterms -> c).
usage: python copycat.py NMAX BUDGET"""
import sys, collections
from dm import *
NMAX, BUD = map(int, sys.argv[1:3])
X = atom("x")
def occ(i):
    memo = {}
    def f(j):
        if j == X: return 1
        if j <= 0: return 0
        if j in memo: return memo[j]
        r = f(L[j]) + f(R[j]); memo[j] = r; return r
    return f(i)
def closed(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True
def skel(i):
    if i == X: return "x"
    if closed(i): return "c"
    args, h = spine(i)
    s = "x" if h == X else "S"
    return s + "".join("(" + skel(a) + ")" for a in args)
cnt = collections.Counter(); ex = {}
for n in range(1, NMAX + 1):
    for C in trees(n):
        args, h = spine(C)
        st = list(reversed(args + [X]))
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
        k = occ(surv)
        if k < 2: continue
        key = (k, skel(surv))
        cnt[key] += 1
        if key not in ex: ex[key] = show(C)
for key, v in sorted(cnt.items(), key=lambda kv: (kv[0][0], len(kv[0][1])))[:60]:
    print(key[0], "%-60s" % key[1], v, "e.g.", ex[key])
print("distinct", len(cnt))
