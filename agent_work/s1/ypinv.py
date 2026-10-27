"""S1 agent: test INV-PY = 'at every list from the first list after D's opening until the glue of w onto y,
if the P-region is non-empty then the first Y-element is the bare y' (single-wrapper transfers of ORDERED
single-occurrence data; split IGEN / non-IGEN; also over ALL proper transfers incl. multi-wrapper: 'any').
Also records which step types consume the Y-top y while |P| >= 1 (violations).
usage: ypinv.py N | ypinv.py rand SEED NMAX COUNT"""
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
    multi = hm.R[V] != Y
    aV, _ = hm.spine(V); k = len(aV)
    igen = any(len(L) >= k and list(reversed(L[-k:])) == aV for L in hist[:-1])
    # end time: glue of the innermost wrapper onto y (first time [a, vn, y]) or the transfer
    t2 = V
    while hm.R[t2] != Y: t2 = hm.R[t2]
    vn = hm.L[t2]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == vn and L[-3] == Y]
    tend = gl[0] if gl else len(hist) - 1
    ok = True; viol = set()
    for t in range(1, tend + 1):
        L = list(reversed(hist[t]))
        np_ = sum(1 for e in L if cls(e) == "P")
        ys = [e for e in L if cls(e) == "Y"]
        if np_ >= 1 and (not ys or ys[0] != Y):
            ok = False
            Lp = list(reversed(hist[t - 1]))
            viol.add(cls(Lp[0]) + cls(Lp[1]) + cls(Lp[2]) + ("/y@2" if Lp[1] == Y else ""))
    return ("multi" if multi else "single", "IGEN" if igen else "nonIGEN", "INV-PY" if ok else "VIOL " + ",".join(sorted(viol)))
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
