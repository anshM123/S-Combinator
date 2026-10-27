"""S1 agent: at every list (before the transfer) where INV-PY fails (P-region non-empty, first Y-element not the
bare y), which P-elements are present relative to the final single wrapper w = b0.c0: equal to c0 / contains c0 /
contains w / unrelated.  Also: creations of w (steps whose new node is w) at such lists.
usage: strand.py N | strand.py rand SEED NMAX COUNT"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ytopinv as YI, wptest as WT
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
    kinds = set(); badcre = 0; allcre = 0
    for t in range(1, len(hist) - 1):
        L = list(reversed(hist[t]))
        if L[1] == b0 and L[2] == c0: 
            allcre += 1
        Pr = [e for e in L if cls(e) == "P"]
        ys = [e for e in L if cls(e) == "Y"]
        if Pr and not (ys and ys[0] == Y):
            for e in Pr:
                if e == c0: kinds.add("c0")
                elif WT.contains(e, w): kinds.add("contains w")
                elif WT.contains(e, c0): kinds.add("contains c0")
                elif WT.contains(c0, e): kinds.add("inside c0")
                else: kinds.add("unrelated")
            if L[1] == b0 and L[2] == c0: badcre += 1
    return ("violations: " + ",".join(sorted(kinds)) if kinds else "no INV-PY violation", "bad creations %d" % badcre, "creations %d" % min(allcre, 3))
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
                hm.truncate(M0); YI._cl.clear(); WT._cw.clear()
    else:
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and pg.ordered(D): feed(D)
            hm.truncate(M0); YI._cl.clear(); WT._cw.clear()
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
