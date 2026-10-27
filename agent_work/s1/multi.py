"""S1 agent: anatomy of MULTI-wrapper handlers V = v1.(v2.(...(vn.y))) of proper transfers from ORDERED
single-occurrence data (non-FH).  For every level j (L_j = v_j.L_{j+1}, L_{n+1} = y) find the step that created the
node L_j ([a_j, v_j, L_{j+1}]) and classify: class of v_j (C/P), front a_j: 'c_j' (= right child of v_j), C, P, Y;
for P-fronts != c_j: did 'c_j run on (v_j, L_{j+1})' (list args(c_j) ++ [v_j, L_{j+1}, ...]) happen before?
Also the next-phase outcome.  usage: multi.py N | multi.py rand SEED NMAX COUNT | multi.py rc N (right combs)"""
import sys, os, collections, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg
import classify as CL
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
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and proper(lst[-3])): return None
    V = lst[-3]; ws = []; levels = []; t = V
    while t != Y: ws.append(hm.L[t]); levels.append(t); t = hm.R[t]
    if len(ws) < 2: return None
    if any(CL.lp_reaches(w) for w in ws): return ("FH",)
    out = []
    aV, _ = hm.spine(V); k = len(aV)
    igen = any(len(L) >= k and list(reversed(L[-k:])) == aV for L in hist)
    for j in range(len(ws) - 1, -1, -1):
        v = ws[j]; below = levels[j + 1] if j + 1 < len(levels) else Y
        cr = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == v and L[-3] == below]
        if not cr: out.append("L%d:none" % (j + 1)); continue
        a = hist[cr[0]][-1]
        if v <= 0 or hm.head(v) != 0: out.append("L%d:v%s-atomhead" % (j + 1, cls(v))); continue
        cj = hm.R[v]
        if a == cj: kind = "alpha"
        else: kind = "front" + cls(a)
        extra = ""
        if kind == "frontP" and hm.head(cj) == 0:
            ac, _ = hm.spine(cj)
            pref = ac + [v, below]
            ran = any(len(L) >= len(pref) and list(reversed(L[-len(pref):])) == pref for L in hist[:cr[0] + 1])
            extra = "/ran" if ran else "/NOTran"
        out.append("L%d:v%s-%s%s" % (j + 1, cls(v), kind, extra))
    o3 = CL.phase3(V)[0]
    return ("n=%d" % len(ws), " ".join(out), "IGEN" if igen else "-", o3)
if __name__ == "__main__":
    st = collections.Counter(); ex = {}
    def feed(D):
        r = info(D)
        if r is not None:
            st[r] += 1
            if r not in ex: ex[r] = hm.show(D)
        _cl.clear()
    mode = sys.argv[1]
    if mode == "rand":
        import r3search as RS
        random.seed(int(sys.argv[2])); N = int(sys.argv[3]); M0 = hm.mark()
        for it in range(int(sys.argv[4])):
            D = RS.rtree(random.randint(4, N), 1)
            if hm.head(D) == 0 and pg.ordered(D): feed(D)
            hm.truncate(M0)
    elif mode == "rc":
        N = int(sys.argv[2])
        for D in c3.rcombs(N):
            if hm.head(D) == 0: feed(D)
    else:
        N = int(mode)
        for n in range(2, N + 1):
            CS = tg.contexts(n); M0 = hm.mark()
            for G in CS:
                D = tg.subst(G, tg.HOLE, P)
                if hm.head(D) == 0 and pg.ordered(D): feed(D)
                hm.truncate(M0)
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
