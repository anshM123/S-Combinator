"""S1 agent: test H2 = 'in a non-IGEN single-wrapper run of ORDERED single-occurrence data, the P-region has
exactly 2 elements at every list from the creation of w (inclusive) to the glue of w onto y (inclusive)'.
Also records the sequence of step types (classes of the first three elements) between creation and glue,
compressed, and |P| before the creation.  usage: h2test.py N | h2test.py rand SEED NMAX COUNT"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ytopinv as YI
hm, tg, pg, P, Y = YI.hm, YI.tg, YI.pg, YI.P, YI.Y
cls = YI.cls
def info(D, budget=1500):
    X, Rr = YI.X, YI.Rr
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    hist.append(tuple(lst))
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and YI.proper(lst[-3])): return None
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
    sizes = set(); types = []
    for t in range(t0 + 1, tgl + 1):
        L = list(reversed(hist[t]))
        sizes.add(sum(1 for e in L if cls(e) == "P"))
        if t < tgl:
            ty = cls(L[0]) + cls(L[1]) + cls(L[2])
            if not types or types[-1] != ty: types.append(ty)
    pre = set()
    for t in range(1, t0 + 1):
        L = list(reversed(hist[t]))
        pre.add(sum(1 for e in L if cls(e) == "P"))
    return (pat, "IGEN" if igen else "nonIGEN", "P-sizes " + str(sorted(sizes)), "pre " + str(sorted(pre)), " ".join(types))
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
                hm.truncate(M0); YI._cl.clear()
    else:
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and pg.ordered(D): feed(D)
            hm.truncate(M0); YI._cl.clear()
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
