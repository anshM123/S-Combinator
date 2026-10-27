"""S1 agent: the form of c0's FIRST hole front in every single-wrapper pattern-beta transfer with a P-front (glue front
a P-term != c0), for ordered single-occurrence data.  Forms (abstract run of args(c0) ++ [h1, h2]):
  none      no hole front (PAF)              h2       second-hole front (a y-call)
  A         h1.h2...  (H1ok)                 bare     bare h1 with h2 at position 3 (H1ok)
  BF1       h1.(X.h1) with h2 at position 3  BF2      h1.(X.h1).h2...      (X: S-headed P-term, hole-free)
  BFp1/BFp2 the same with X p-headed         BFc      the same with X closed            other
plus NK1(b0).  The machine-checked r3_single3 covers A, bare, BF1, BF2 and any form with NK1(b0).
usage: bfcheck.py N [N0] | bfcheck.py rand SEED NMAX COUNT"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover6 as C6, resid as RD
hm, tg, pg, P, Y, X, Rr = C6.hm, C6.tg, C6.pg, C6.P, C6.Y, C6.X, C6.Rr
H1, H2 = RD.H1, RD.H2
def form(c0):
    k, L = RD.front(c0, H1, H2, budget=50000)
    if k == "budget": return "BUDGET"
    if k == "hnf": return "none"
    g = L[0]; h = hm.head(g)
    if h == H2: return "h2"
    if h != H1: return "none"
    a, _ = hm.spine(g)
    if a and a[0] == H2: return "A"
    if not a: return "bare" if len(L) >= 3 and L[2] == H2 else "other(bare)"
    x = a[0]
    if x > 0 and hm.R[x] == H1:
        Xt = hm.L[x]; at = tg.atoms(Xt) if Xt > 0 else {Xt: 1}
        if at.get(H1, 0) or at.get(H2, 0): return "other(X holes)"
        hX = hm.head(Xt)
        tag = "BF" if (hX == 0 and at.get(P, 0)) else ("BFp" if hX == P else ("BFc" if not at.get(P, 0) else "BFo"))
        if len(a) == 1 and len(L) >= 3 and L[2] == H2: return tag + "1"
        if len(a) >= 2 and a[1] == H2: return tag + "2"
    return "other"
def betaP(D):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and RD.proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return None
    w = hm.L[V]
    if w <= 0 or hm.head(w) != 0: return None
    b0, c0 = hm.L[w], hm.R[w]
    if c0 <= 0 or hm.head(c0) != 0 or b0 <= 0 or hm.head(b0) != 0: return None
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    a1 = hist[gl[0]][-1]
    if a1 == c0 or not tg.atoms(a1).get(P, 0): return None
    return b0, c0
if __name__ == "__main__":
    st = collections.Counter(); ex = {}
    def feed(D):
        r = betaP(D)
        if r is None: return
        b0, c0 = r
        k = (form(c0), "NK1" if C6.nk1(b0) else "calls-k1")
        st[k] += 1
        if k not in ex: ex[k] = hm.show(D)
    if sys.argv[1] == "rand":
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and pg.ordered(D): feed(D)
            hm.truncate(M0)
    else:
        N = int(sys.argv[1]); N0 = int(sys.argv[2]) if len(sys.argv) > 2 else 2
        for n in range(N0, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and pg.ordered(D): feed(D)
                hm.truncate(M0)
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, k, ex[k])
