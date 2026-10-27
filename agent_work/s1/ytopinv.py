"""S1 agent: test INV-Y.  For single-wrapper transfers (w = b0.c0 S-headed) of ORDERED single-occurrence data:
IGEN = phase 2 lays out args(w.y) (list starting with args(b0) ++ [c0, y]) at some time before its transfer.
INV-Y = from the creation of w (first step creating the node b0.c0) until the glue of w onto y, the first
Y-element of every list is the bare y.  Also: number of P-elements <= 2 throughout (Lemma AB).
Reports counts by (pattern, IGEN?, INV-Y?, |P|<=2?).
usage: ytopinv.py N  |  ytopinv.py rand SEED NMAX COUNT"""
import sys, os, collections, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
_cl = {}
def cls(t):
    r = _cl.get(t)
    if r is None:
        a = tg.atoms(t)
        r = "Y" if (a.get(X, 0) or a.get(Y, 0) or a.get(Rr, 0)) else ("P" if a.get(P, 0) else "C")
        _cl[t] = r
    return r
def proper(V):
    a = tg.atoms(V)
    return V != Y and a.get(Y, 0) == 1 and not a.get(X, 0) and not a.get(Rr, 0)
def info(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    hist.append(tuple(lst))
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return None
    w = hm.L[V]
    if w <= 0 or hm.head(w) != 0: return None
    b0, c0 = hm.L[w], hm.R[w]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    tgl = gl[0]; a1 = hist[tgl][-1]
    pat = "alpha" if a1 == c0 else ("beta-P" if cls(a1) == "P" else "beta-C")
    cr = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == b0 and L[-3] == c0]
    if not cr: return (pat, "no creation")
    t0 = cr[0]
    aV, _ = hm.spine(V); k = len(aV)
    igen = any(len(L) >= k and list(reversed(L[-k:])) == aV for L in hist[:-1])
    invy = True; p2 = True
    for t in range(t0 + 1, tgl + 1):
        L = list(reversed(hist[t]))
        ys = [e for e in L if cls(e) == "Y"]
        if not ys or ys[0] != Y: invy = False
        if sum(1 for e in L if cls(e) == "P") > 2: p2 = False
    return (pat, "IGEN" if igen else "nonIGEN", "INV-Y" if invy else "Ytop changes", "|P|<=2" if p2 else "|P|>2")
if __name__ == "__main__":
    st = collections.Counter(); ex = {}
    def feed(D):
        r = info(D)
        if r is not None:
            st[r] += 1
            if r not in ex: ex[r] = hm.show(D)
    if sys.argv[1] != "rand":
        N = int(sys.argv[1])
        for n in range(2, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and pg.ordered(D): feed(D)
                hm.truncate(M0); _cl.clear()
    else:
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and pg.ordered(D): feed(D)
            hm.truncate(M0); _cl.clear()
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
