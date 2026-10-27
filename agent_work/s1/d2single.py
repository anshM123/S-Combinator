"""S1 agent: Church chains - classify the transfers of the SECOND datum D_2 = V_1[y:=p, p:=c1]: FH (some wrapper
of V_2 has its leftmost path at p or a frozen atom), single-wrapper glue pattern (alpha: front = c0; closed front;
beta-P: P-front != c0, with H1ok(c0) / NK1(b0) status), multi-wrapper.
usage: d2single.py one N | d2single.py rand SEED NMAX COUNT"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multi as MU, resid as RD
hm, tg, c3, pg, P, Y, X, Rr = MU.hm, MU.tg, MU.c3, MU.pg, MU.P, MU.Y, MU.X, MU.Rr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
import target3 as T3, classify as CL, h1ok as H1
def classify2(D2):
    lst = [Rr, Y, X, D2]; hist = []
    for t in range(2000):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    V = lst[-3]
    ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    if any(CL.lp_reaches(w) for w in ws): return ("FH", "multi" if len(ws) > 1 else "single")
    if len(ws) > 1: return ("non-FH multi",)
    w = ws[0]
    if w <= 0 or hm.head(w) != 0: return ("w atom/atom-headed",)
    b0, c0 = hm.L[w], hm.R[w]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    if not gl: return ("no glue?",)
    a1 = hist[gl[0]][-1]
    if a1 == c0: return ("single", "alpha")
    if not tg.atoms(a1).get(P, 0): return ("single", "closed front")
    k, Lb = RD.front(b0, RD.K1, RD.K2) if b0 > 0 else ("front", [RD.K1, RD.K2])
    nk1 = not (k == "front" and hm.head(Lb[0]) == RD.K1)
    return ("single", "beta-P", H1.h1ok(c0) if hm.head(c0) == 0 else "c0 atom-headed", "NK1" if nk1 else "b0 calls k1")
def feed(D1, st, ex):
    o, V, _ = T3.phase(D1, 2000)
    if o != "proper3": return
    D2 = tg.subst(tg.subst(V, P, c3.FROZ[0]), Y, P)
    o2, V2, _ = T3.phase(D2, 2000)
    if o2 != "proper3": return
    k = classify2(D2)
    st[k] += 1
    if k not in ex: ex[k] = hm.show(D1) + " -> D2 " + hm.show(D2)
if __name__ == "__main__":
    st = collections.Counter(); ex = {}
    if sys.argv[1] == "one":
        N = int(sys.argv[2])
        for n in range(2, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0: feed(D, st, ex)
                hm.truncate(M0); MU._cl.clear()
    else:
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), random.choice([1, 2]))
            if hm.head(D) == 0: feed(D, st, ex)
            hm.truncate(M0); MU._cl.clear()
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
