"""Single-datum DM: start from a random right-comb stack w1.(w2.(...(wk.X))) over an opaque base X with symbols drawn
from small closed terms; run the DM; at each round end record (#occurrences of X in survivor, depth of right-comb
layers over X if the survivor is a right comb over X).  Report runs where X stays single and the layer depth exceeds
the initial depth by >= GROW (i.e. genuine stack growth without copying the base)."""
import sys, random
from dm import *
SEED, NRUNS, MAXSYM, K, BUDGET, GROW = map(int, sys.argv[1:7])
random.seed(SEED)
X = atom("X")
syms = []
for n in range(1, MAXSYM + 1): syms += trees(n)
def occ(i, a):
    c = 0; st = [i]
    while st:
        j = st.pop()
        if j == a: c += 1
        elif j > 0: st.append(L[j]); st.append(R[j])
    return c
def closed(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True
def comb_depth(t):
    """t = c1.(c2.(...(cm.X))) with closed c_i -> m, else None"""
    d = 0
    while t != X:
        if t <= 0: return None
        if not closed(L[t]): return None
        t = R[t]; d += 1
    return d
hits = 0
for run in range(NRUNS):
    m0 = mark()
    word = [random.choice(syms) for _ in range(K)]
    t = X
    for w in reversed(word): t = app(w, t)
    st = list(reversed(spine(t)[0]))
    if spine(t)[1] != 0: truncate(m0); continue
    maxd = 0; rounds = 0; single = True; trace = []
    for step in range(BUDGET):
        n = len(st)
        if n >= 3:
            a = st[-1]; args, h = spine(a)
            if h != 0: break
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(args))
        elif n >= 1:
            c = st[-1]; rounds += 1
            o = occ(c, X)
            if o != 1: single = False; break
            d = comb_depth(c)
            if d is not None:
                trace.append(d); maxd = max(maxd, d)
            args, h = spine(c)
            if h != 0: break
            st.clear(); st.extend(reversed(args))
        else:
            break
    if single and maxd >= K + GROW:
        hits += 1
        print("word=%s trace=%s" % ([show(w) for w in word], trace[:40]), flush=True)
    truncate(m0)
print("hits", hits)
