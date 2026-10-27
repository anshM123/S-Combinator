"""S1 agent (cover5: + IL-ATOM + IL-NH): coverage of proper position-3 transfers of ORDERED single-occurrence data by the machine-checked
theorems after today's work (R3G.lean), first class that applies:
  FH        some wrapper p-/frozen-headed or with leftmost path to p/frozen (OTD/FH1/FHL)        [no condition]
  PAH       single wrapper, c0 atom-headed (R3F pah_main)                                     [no condition]
  ALPHA     single wrapper, glue front = c0 (r3_single -> alpha_main)                          [no condition]
  CLOSED    single wrapper, glue front closed (r3_single -> closedglue_main)                  [no condition]
  S1+H1ok   single wrapper, glue front a P-term != c0, H1ok(c0) (r3_single: s1_core + beta_main)
  S1+NK1    single wrapper, glue front a P-term != c0, b0 never calls its first hole (r3_single2 -> paxb_main)
  open-single
  IGEN      multi-wrapper, phase 2 lays out args(V) (igen_main)                               [no condition]
  NHALL     multi-wrapper, every level's c_j never calls its holes (nhall_main)          [handler condition]
  multi-other (PAMF / LN0 / open)
usage: cover5.py N | cover5.py rand SEED NMAX COUNT | cover5.py rc N"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import resid as RD
hm, tg, c3, pg, P, Y, X, Rr = RD.hm, RD.tg, RD.c3, RD.pg, RD.P, RD.Y, RD.X, RD.Rr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
import classify as CL, h1ok as H1, fc0
def nk1(b0):
    if b0 <= 0: return True
    k, Lb = RD.front(b0, RD.K1, RD.K2)
    return not (k == "front" and hm.head(Lb[0]) == RD.K1)
def classify(D, budget=1500):
    lst = [Rr, Y, X, D]; hist = []
    for t in range(budget):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and RD.proper(lst[-3])): return None
    V = lst[-3]; ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    o3 = CL.phase3(V)[0]
    if any(CL.lp_reaches(w) for w in ws): return ("FH", o3)
    if len(ws) == 1:
        w = ws[0]
        if w <= 0 or hm.head(w) != 0: return ("open-single (w atom-headed)", o3)
        b0, c0 = hm.L[w], hm.R[w]
        if hm.head(c0) != 0: return ("PAH", o3)
        gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y]
        a1 = hist[gl[0]][-1]
        if a1 == c0: return ("ALPHA", o3)
        if not tg.atoms(a1).get(P, 0): return ("CLOSED", o3)
        ac0, _ = hm.spine(c0)
        s1 = any(len(L) >= len(ac0) + 2 and list(reversed(L[-(len(ac0) + 2):])) == ac0 + [w, Y] for L in hist)
        if not s1: return ("S1 FAILS?!", o3)
        if H1.h1ok(c0) != "H1 RESIDUAL": return ("S1+H1ok", o3)
        if nk1(b0): return ("S1+NK1", o3)
        return ("open-single", o3)
    aV, _ = hm.spine(V); k = len(aV)
    if any(len(L) >= k and list(reversed(L[-k:])) == aV for L in hist): return ("IGEN", o3)
    vn = ws[-1]
    if vn > 0 and hm.head(vn) == 0 and hm.L[vn] > 0 and hm.head(hm.L[vn]) == 0 and hm.R[vn] < 0 and hm.R[vn] != Y:
        Ln = hm.app(vn, Y); aL, _ = hm.spine(Ln); kl = len(aL)
        if any(len(L) >= kl and list(reversed(L[-kl:])) == aL for L in hist): return ("IL-ATOM", o3)
    if vn > 0 and hm.head(vn) == 0 and hm.L[vn] > 0 and hm.head(hm.L[vn]) == 0 and hm.R[vn] > 0 and hm.head(hm.R[vn]) == 0:
        Ln = hm.app(vn, Y); aL, _ = hm.spine(Ln); kl = len(aL)
        if any(len(L) >= kl and list(reversed(L[-kl:])) == aL for L in hist) and fc0.F(hm.R[vn]) not in ("h1", "h2"):
            return ("IL-NH", o3)
    if len(ws) == 2 and all(w > 0 and hm.head(w) == 0 and hm.head(hm.R[w]) == 0 for w in ws):
        v1, v2 = ws; L2 = hm.app(v2, Y)
        g2 = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-1] == hm.R[v2] and L[-2] == v2 and L[-3] == Y]
        g1 = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-1] == hm.R[v1] and L[-2] == v1 and L[-3] == L2]
        if g2 and g1 and g2[0] < g1[-1]:
            il2 = any(CL.pre(L[-1], L2) for L in hist[g2[0] + 1:])
            if not il2: return ("MWA2", o3)
            return ("I-L2 (nested alpha)", o3)
    allnh = all(w > 0 and hm.head(w) == 0 and hm.head(hm.R[w]) == 0 and fc0.F(hm.R[w]) not in ("h1", "h2") for w in ws)
    if allnh: return ("NHALL", o3)
    return ("multi-other", o3)
if __name__ == "__main__":
    st = collections.Counter(); ex = {}
    def feed(D):
        r = classify(D)
        if r is not None:
            st[r] += 1
            if r not in ex: ex[r] = hm.show(D)
    if sys.argv[1] == "rand":
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
        N = int(sys.argv[1])
        for n in range(2, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and pg.ordered(D): feed(D)
                hm.truncate(M0)
    tot = collections.Counter()
    for (k, o3), v in st.items(): tot[k] += v
    print("TOTAL", sum(tot.values()), dict(tot))
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
