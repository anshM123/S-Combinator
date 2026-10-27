"""S1 agent: anatomy of MULTI-wrapper proper transfers (>= 2 wrappers, not FH, not IGEN) of ordered single-occurrence
data.  For the innermost wrapper vn = bn.cn: glue pattern of vn.y (alpha: front cn; closed; beta: other P-front),
whether phase 2 re-opens the innermost level (I-Ln: args(bn) ++ [cn, y] on top after the glue), the first hole front
of cn's two-hole run (h1 / h2 / none) and of bn's (k1 / k2 / none); same for the outer wrapper v1 (glue onto L2).
usage: mwcheck.py N [N0] | mwcheck.py rand SEED NMAX COUNT | mwcheck.py rc N"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover6 as C6, resid as RD
hm, tg, pg, c3, P, Y, X, Rr = C6.hm, C6.tg, C6.pg, C6.c3, C6.P, C6.Y, C6.X, C6.Rr
H1, H2, K1, K2 = RD.H1, RD.H2, RD.K1, RD.K2
def fh(code, z1, z2):
    if code <= 0 or hm.head(code) != 0: return "atom"
    k, L = RD.front(code, z1, z2, budget=50000)
    if k == "budget": return "BUDGET"
    if k == "hnf": return "none"
    h = hm.head(L[0])
    return "1" if h == z1 else ("2" if h == z2 else "none")
def glue_pattern(hist, v, Lb):
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == v and L[-3] == Lb]
    if not gl: return None, None
    a = hist[gl[0]][-1]
    c = hm.R[v] if v > 0 else None
    if a == c: return "alpha", gl[0]
    if not tg.atoms(a).get(P, 0) if a > 0 else a != P: return "closed", gl[0]
    return "beta", gl[0]
def anatomy(D):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and RD.proper(lst[-3])): return None
    V = lst[-3]; ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    if len(ws) < 2: return None
    r = C6.classify(D)
    if r is None or r[0] in ("FH", "IGEN"): return None
    vn = ws[-1]
    if vn <= 0 or hm.head(vn) != 0: return ("n=%d" % len(ws), r[0], "vn atom-headed")
    bn, cn = hm.L[vn], hm.R[vn]
    pat, tgl = glue_pattern(hist, vn, Y)
    Ln = hm.app(vn, Y); aL, _ = hm.spine(Ln); kl = len(aL)
    reopen = tgl is not None and any(len(L) >= kl and list(reversed(L[-kl:])) == aL for L in hist[tgl + 1:])
    Lb = Y
    for w in reversed(ws[1:]): Lb = hm.app(w, Lb)
    v1 = ws[0]
    pat1, _ = glue_pattern(hist, v1, Lb) if v1 > 0 else (None, None)
    return ("n=%d" % len(ws), r[0], "inner " + str(pat), "reopen" if reopen else "no-reopen",
            "c_n:" + fh(cn, H1, H2), "b_n:" + fh(bn, K1, K2), "outer " + str(pat1),
            "c_1:" + (fh(hm.R[v1], H1, H2) if v1 > 0 else "-"))
if __name__ == "__main__":
    st = collections.Counter(); ex = {}
    def feed(D):
        r = anatomy(D)
        if r is None: return
        st[r] += 1
        if r not in ex: ex[r] = hm.show(D)
    if sys.argv[1] == "rand":
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and pg.ordered(D): feed(D)
            hm.truncate(M0)
    elif sys.argv[1] == "rc":
        for D in c3.rcombs(int(sys.argv[2])):
            if hm.head(D) == 0: feed(D)
    else:
        N = int(sys.argv[1]); N0 = int(sys.argv[2]) if len(sys.argv) > 2 else 2
        for n in range(N0, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and pg.ordered(D): feed(D)
                hm.truncate(M0)
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
