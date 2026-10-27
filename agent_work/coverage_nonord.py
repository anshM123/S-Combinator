"""NON-ordered data D = G[p] (S-headed 1-hole contexts <= N leaves that are not ordered): proper transfers are clean
(handler without p) or dirty.  Dirty ones: machine-checked coverage and whether the next phase transfers properly.
Clean ones: the next datum is an ordered right comb (phase-2 data of the main study)."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, phase2_general as pg
import coverage_all as CA
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
N = int(sys.argv[1]); st = collections.Counter(); openex = []
for n in range(2, N + 1):
    CS = tg.contexts(n); M0 = hm.mark()
    for G in CS:
        D = tg.subst(G, tg.HOLE, P)
        if hm.head(D) != 0 or pg.ordered(D): hm.truncate(M0); continue
        o2, V, _ = T3.phase(D, 1500)
        if o2 != "proper3": hm.truncate(M0); continue
        clean = P not in tg.atoms(V)
        D3 = tg.subst(tg.subst(V, P, C), Y, P)
        o3, V3, _ = T3.phase(D3, 1500)
        nx = "next proper" if o3 == "proper3" else "next not proper"
        if clean:
            st[("clean", nx)] += 1
        else:
            r = CA.classify(D)
            st[("dirty", r[0] if r else "?", nx)] += 1
            if r and r[0] == "open" and len(openex) < 6: openex.append(hm.show(D))
        hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
for e in openex: print("open:", e)
