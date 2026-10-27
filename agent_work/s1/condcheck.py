"""S1 agent: are the handler-only conditions used by cover6.py DECIDED (not budget-limited)?  For every transfer that
cover6.py puts in S1+H1ok, S1+NK1, IL-NH or NHALL, recompute the abstract run of the relevant code (c0 on two holes for
H1ok / NH, b0 for NK1) with a 50,000-step budget and report whether it reaches an atom-headed front (or a short list),
i.e. whether the condition is certified, or remains budget-limited (then the condition is only 'not refuted').
usage: condcheck.py N [N0] | condcheck.py rand SEED NMAX COUNT | condcheck.py rc N"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover6 as C6, resid as RD
hm, tg, pg, P, Y, X, Rr, c3 = C6.hm, C6.tg, C6.pg, C6.P, C6.Y, C6.X, C6.Rr, C6.c3
H1, H2 = RD.H1, RD.H2
def decided(code, budget=50000):
    if code <= 0: return "S/atom"
    a, h = hm.spine(code)
    if h != 0: return "atom-headed"
    st = [H2, H1] + list(reversed(a))
    for t in range(budget):
        if len(st) < 3: return "decided"
        if hm.head(st[-1]) != 0: return "decided"
        hm.step(st)
    return "BUDGET"
def wrappers(D):
    lst = [Rr, Y, X, D]
    s, k = hm.run(lst, 1500)
    V = lst[-3]; ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    return ws
if __name__ == "__main__":
    st = collections.Counter(); ex = {}
    def feed(D):
        r = C6.classify(D)
        if r is None or r[0] not in ("S1+H1ok", "S1+NK1", "IL-NH", "NHALL"): return
        ws = wrappers(D)
        if r[0] == "S1+H1ok": codes = [hm.R[ws[-1]]]
        elif r[0] == "S1+NK1": codes = [hm.L[ws[-1]]]
        elif r[0] == "IL-NH": codes = [hm.R[ws[-1]]]
        else: codes = [hm.R[w] for w in ws]
        res = tuple(decided(cd) for cd in codes)
        k = (r[0], "all decided" if all(x != "BUDGET" for x in res) else "BUDGET")
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
