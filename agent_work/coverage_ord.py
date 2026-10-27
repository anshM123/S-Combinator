"""Combined coverage for GENERAL ORDERED data D = G[p] (all S-headed ordered 1-hole contexts G with <= N leaves):
every proper position-3 transfer is classified by the first machine-checked theorem (FH/FHL/YD/PA/PB/PAM) whose
hypotheses it satisfies; also counted: does the next phase make a proper transfer?"""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, phase2_general as pg
import coverage_all as CA
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
N = int(sys.argv[1]); st = collections.Counter(); nxt = collections.Counter(); openex = []
for n in range(2, N + 1):
    CS = tg.contexts(n); M0 = hm.mark()
    for G in CS:
        D = tg.subst(G, tg.HOLE, P)
        if hm.head(D) != 0 or not pg.ordered(D): hm.truncate(M0); continue
        r = CA.classify(D)
        if r is not None:
            st[r] += 1
            if r[0] == "open" and len(openex) < 6: openex.append(hm.show(D))
            o2, V, _ = T3.phase(D, 1500)
            D3 = tg.subst(tg.subst(V, P, C), Y, P)
            o3, V3, _ = T3.phase(D3, 1500)
            nxt["next phase proper" if o3 == "proper3" else "next phase not proper"] += 1
        hm.truncate(M0)
tot = sum(st.values())
for k in sorted(st): print(k, st[k])
print("total", tot, " covered", tot - sum(v for k, v in st.items() if k[0] == "open"))
print(dict(nxt))
for e in openex: print("open:", e)
