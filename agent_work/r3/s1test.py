"""R3 agent: structural claim (S1) on ALL S-headed data with one occurrence of p (1-hole contexts, ordered or not)
and with two occurrences: for every proper single-wrapper transfer glued in pattern beta, does phase 2 run c0 on
(w, y) (list args(c0) ++ [w, y, ...]) before the glue?  usage: s1test.py one N | s1test.py two N"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classify as CL, r3census as RC, h1ok as H1, fc0
hm, tg, c3, T3, pg = CL.hm, CL.tg, CL.c3, CL.T3, RC.pg
P, Y, X, Rr = CL.P, CL.Y, CL.X, CL.Rr
def startswith(L, pref):
    k = len(pref)
    return len(L) >= k and list(reversed(L[-k:])) == pref
def info(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3])): return None
    V = lst[-3]
    if hm.R[V] != Y: return None
    w = hm.L[V]
    if w <= 0: return ("w = S",)
    if CL.lp_reaches(w) or hm.head(w) != 0: return ("FH",)
    b0, c0 = hm.L[w], hm.R[w]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
    tg_ = gl[0]; a1 = hist[tg_][-1]
    if a1 == c0: return ("alpha",)
    if hm.head(c0) != 0: return ("beta, c0 not S-headed",)
    ac0, _ = hm.spine(c0)
    before = any(startswith(L, ac0 + [w, Y]) for L in hist[:tg_ + 1])
    aV, _ = hm.spine(V)
    igen = any(startswith(L, aV) for L in hist)
    o3 = CL.phase3(V)[0]
    return ("beta", "ordered" if pg.ordered(D) else "non-ordered",
            "c0 on (w,y) before glue" if before else "NO c0 on (w,y)", "Igen" if igen else "-",
            "F(c0)=" + fc0.F(c0), H1.h1ok(c0), o3)
if __name__ == "__main__":
    mode, N = sys.argv[1], int(sys.argv[2])
    st = collections.Counter(); ex = collections.defaultdict(list)
    def feed(D):
        r = info(D)
        if r is not None and r[0] == "beta":
            st[r] += 1
            if len(ex[r]) < 2: ex[r].append(hm.show(D))
    if mode == "one":
        for n in range(2, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0: feed(D)
                hm.truncate(M0)
    else:
        for n in range(3, N + 1):
            for (t, a, b) in RC.two_hole(n):
                M0 = hm.mark()
                D = RC.place(t, {a, b})
                if hm.head(D) == 0: feed(D)
                hm.truncate(M0)
    for k in sorted(st): print(k, st[k], ex[k])
