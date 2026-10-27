import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover5 as C5, multi as MU
hm, tg, pg, P = C5.hm, C5.tg, C5.pg, C5.P
N = int(sys.argv[1])
for n in range(2, N + 1):
    CS = tg.contexts(n); M0 = hm.mark()
    for G in CS:
        D = tg.subst(G, tg.HOLE, P)
        if hm.head(D) == 0 and pg.ordered(D):
            r = C5.classify(D)
            if r is not None and r[0] == "multi-other":
                print(hm.show(D), r, MU.info(D))
        hm.truncate(M0)
