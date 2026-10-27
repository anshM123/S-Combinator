"""R3 agent: re-run the next phases that hit the 2000-step budget in the single-occurrence censuses with a larger
budget.  usage: budget_recheck.py one N BUDGET | budget_recheck.py rcomb N BUDGET"""
import sys, os, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, phase2_general as pg
import rcomb_census as RCC
P, Y = c3.P, c3.Y
def phase_len(D, budget):
    st = [c3.Rr, Y, c3.X, D]
    s, k = hm.run(st, budget)
    if s != "stuck": return s, len(st)
    h = hm.head(st[-1])
    if h == P:
        return ("proper3" if len(st) >= 3 and T3.S3.proper(st[-3]) else "pfront"), len(st)
    if h == c3.FROZ[0]: return "reexec", len(st)
    return "front-other", len(st)
if __name__ == "__main__":
    mode, N, B = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    st = collections.Counter()
    if mode == "one":
        data = []
        CS = tg.contexts(N)
        for G in CS:
            D = tg.subst(G, tg.HOLE, P)
            if hm.head(D) == 0 and pg.ordered(D): data.append(D)
    else:
        data = [D for D in RCC.rcombs_exact(N) if hm.head(D) == 0]
    M0 = hm.mark()
    for D in data:
        o2, V, _ = T3.phase(D, 2000)
        if o2 != "proper3": hm.truncate(M0); continue
        D3 = tg.subst(tg.subst(V, P, c3.FROZ[0]), Y, P)
        o3, V3, _ = T3.phase(D3, 2000)
        if o3 == "budget":
            o, ln = phase_len(D3, B)
            st[("rechecked with budget %d" % B, o)] += 1
        hm.truncate(M0)
    for k in sorted(st): print(k, st[k])
