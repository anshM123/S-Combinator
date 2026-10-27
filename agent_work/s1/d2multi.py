"""S1 agent: Church chains - for every SECOND datum D_2 = V_1[y:=p, p:=c1] (V_1 the handler of a proper transfer
of D_1) that makes a proper transfer, report single/multi wrapper and the multi.py anatomy (FH or level glue
patterns).  D_1: all S-headed 1-hole data <= N leaves (mode one) or random (mode rand SEED NMAX COUNT).
usage: d2multi.py one N | d2multi.py rand SEED NMAX COUNT"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multi as MU
hm, tg, c3, pg, P, Y = MU.hm, MU.tg, MU.c3, MU.pg, MU.P, MU.Y
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
import target3 as T3
def feed(D1, st, ex):
    o, V, _ = T3.phase(D1, 2000)
    if o != "proper3": return
    D2 = tg.subst(tg.subst(V, P, c3.FROZ[0]), Y, P)
    o2, V2, _ = T3.phase(D2, 2000)
    if o2 != "proper3": return
    single = hm.R[V2] == Y
    if single:
        k = ("D2 transfer single-wrapper",)
    else:
        r = MU.info(D2)
        k = ("D2 transfer multi",) + (r if r else ("?",))
    st[k] += 1
    if k not in ex: ex[k] = hm.show(D1)
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
