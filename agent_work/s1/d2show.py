"""S1 agent: show Church chains whose second transfer is multi-wrapper: D1, V1, D2, V2 and the FH wrapper of V2."""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multi as MU
hm, tg, c3, pg, P, Y = MU.hm, MU.tg, MU.c3, MU.pg, MU.P, MU.Y
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r3"))
import target3 as T3, classify as CL
N = int(sys.argv[1]); shown = 0
for n in range(2, N + 1):
    CS = tg.contexts(n); M0 = hm.mark()
    for G in CS:
        D = tg.subst(G, tg.HOLE, P)
        if hm.head(D) != 0: hm.truncate(M0); continue
        o, V, _ = T3.phase(D, 2000)
        if o != "proper3": hm.truncate(M0); continue
        D2 = tg.subst(tg.subst(V, P, c3.FROZ[0]), Y, P)
        o2, V2, _ = T3.phase(D2, 2000)
        if o2 != "proper3" or hm.R[V2] == Y: hm.truncate(M0); continue
        ws = []; t = V2
        while t != Y: ws.append(hm.L[t]); t = hm.R[t]
        fh = [hm.show(w) for w in ws if CL.lp_reaches(w)]
        print("D1", hm.show(D), "| V1", hm.show(V), "| D2", hm.show(D2), "| V2", hm.show(V2), "| FH wrappers", fh)
        shown += 1
        hm.truncate(M0)
