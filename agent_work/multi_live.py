"""Live multi-wrapper handlers (no wrapper with a leftmost path to p, outermost wrapper not bare S): in phase 3, is
the bare p' ever exposed (does any list contain p' as an element)?  How does phase 3 end?"""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, fhl_cover as FC
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
if sys.argv[1] == "t":
    NK, WK, NT = map(int, sys.argv[2:5])
    Ks = [t for n in range(1, NK + 1) for t in hm.trees(n) if hm.head(t) == 0]
    wr = [t for n in range(1, WK + 1) for t in hm.trees(n)]
    tails = [P]; fr = [(P, 1)]
    while fr:
        nf = []
        for t, sz in fr:
            for d in wr:
                if sz + hm.size(d) <= NT:
                    u = hm.app(d, t); tails.append(u); nf.append((u, sz + hm.size(d)))
        fr = nf
    data = [hm.app(K, T) for T in tails if T != P for K in Ks]
else:
    data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark()
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3" or hm.R[V] == Y: hm.truncate(M0); continue
    ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    if any(FC.lp_reaches_p(w) for w in ws) or ws[0] == 0: hm.truncate(M0); continue
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    s3 = [Rr, Y, X, D3]; exposed = False
    for t in range(3000):
        if P in s3: exposed = True
        if len(s3) < 3 or hm.head(s3[-1]) != 0: break
        hm.step(s3)
    if P in s3: exposed = True
    h = hm.head(s3[-1]); out = "reexec" if h == C else ("p'-front" if h == P else ("call " + hm.NAMES.get(h, "?") if h < 0 else "other"))
    st[(len(ws) if len(ws) < 4 else "4+", "p' exposed" if exposed else "p' never exposed", out)] += 1
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
