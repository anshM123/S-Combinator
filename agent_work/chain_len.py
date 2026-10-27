"""Church-chain length census: from every S-headed datum D = G[p] (1-hole contexts <= N leaves, ordered or not),
follow proper position-3 transfers D_{j+1} = V_j[y := p, p := c_j] until no proper transfer; record the number of
proper transfers and whether each later datum is ordered and each later handler innermost-dirty."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, phase2_general as pg
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
N = int(sys.argv[1]); st = collections.Counter(); ex = {}
for n in range(2, N + 1):
    CS = tg.contexts(n); M0 = hm.mark()
    for G in CS:
        D = tg.subst(G, tg.HOLE, P)
        if hm.head(D) != 0: hm.truncate(M0); continue
        ln = 0; later_unordered = False; later_clean = False; D0 = D
        for ph in range(6):
            o, V, _ = T3.phase(D, 2000)
            if o != "proper3": break
            ln += 1
            inner = V
            while hm.R[inner] != Y: inner = hm.R[inner]
            if ln >= 2 and P not in tg.atoms(hm.L[inner]): later_clean = True
            D = tg.subst(tg.subst(V, P, c3.FROZ[ph]), Y, P)
            if not pg.ordered(D): later_unordered = True
        st[("chain length %d" % ln, "first datum ordered" if pg.ordered(D0) else "first datum not ordered")] += 1
        if later_unordered: st["a later datum NOT ordered (!)"] += 1
        if later_clean: st["a later handler innermost-clean (!)"] += 1
        ex.setdefault(ln, hm.show(D0))
        hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
for k in sorted(ex): print("example length", k, ex[k])
