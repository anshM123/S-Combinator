"""S1 agent: the handler-only property PF(bn, cn) for the innermost wrapper vn = bn.cn of multi-wrapper proper
transfers: the run of args(bn) ++ [cn, k2] (k2 a fresh atom standing for the new predecessor p') reaches a p-headed
front (then, in the next phase, the image of that front is c-headed, i.e. stuck, and p' never reaches the front).
Outcomes: PF (p-front), K2 (k2-front), hnf (fewer than 3 elements), other (frozen/x/y/r front), BUDGET.
usage: pfcheck.py N [N0] | pfcheck.py rand SEED NMAX COUNT | pfcheck.py rc N   (append 'tailN': N fresh tail atoms (default 12)
after k2, i.e. the replay on args(bn) ++ [cn, k2, t0, ..., t11]; outcome TAIL = a tail atom reaches the front)"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover6 as C6, resid as RD
hm, tg, pg, c3, P, Y, X, Rr = C6.hm, C6.tg, C6.pg, C6.c3, C6.P, C6.Y, C6.X, C6.Rr
K2 = RD.K2
TAIL = []
if len(sys.argv) > 1 and sys.argv[-1].startswith("tail"):
    nt = int(sys.argv[-1][4:] or "12")
    TAIL = [hm.atom("t%d" % i) for i in range(nt)]; sys.argv = sys.argv[:-1]
def pf(bn, cn, budget=50000):
    if bn <= 0:
        a = []
        if bn != 0: return "bn atom"
    else:
        if hm.head(bn) != 0: return "bn atom-headed"
        a, _ = hm.spine(bn)
    st = list(reversed(TAIL)) + [K2, cn] + list(reversed(a))
    for t in range(budget):
        if len(st) < 3:
            return "hnf" if hm.head(st[-1]) == 0 else ("PF" if hm.head(st[-1]) == P else ("K2short" if hm.head(st[-1]) == K2 else "other"))
        h = hm.head(st[-1])
        if h != 0:
            if h == P: return "PF"
            if h == K2:
                if len(st) < 3: return "K2short"
                return "K2(pos3 tail)" if st[-3] in TAIL else "K2"
            return "TAIL" if h in TAIL else "other"
        hm.step(st)
    return "BUDGET"
def check(D):
    lst = [Rr, Y, X, D]
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and RD.proper(lst[-3])): return None
    V = lst[-3]; ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    if len(ws) < 2: return None
    r = C6.classify(D)
    vn = ws[-1]
    if vn <= 0: return (r[0], "vn atom")
    return (r[0], pf(hm.L[vn], hm.R[vn]))
if __name__ == "__main__":
    st = collections.Counter(); ex = {}
    def feed(D):
        r = check(D)
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
    for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, k, ex[k])
