import sys
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, fhl_cover as FC
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
M0 = hm.mark(); shown = 0
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3" or hm.R[V] == Y: hm.truncate(M0); continue
    ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    if any(FC.lp_reaches_p(w) for w in ws) or ws[0] == 0: hm.truncate(M0); continue
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    s3 = [Rr, Y, X, D3]; lines = []; exp_at = None
    for t in range(60):
        lines.append(hm.show_list(s3, maxn=8)[:200].replace("p", "p'"))
        if P in s3 and exp_at is None: exp_at = t
        if len(s3) < 3 or hm.head(s3[-1]) != 0: break
        hm.step(s3)
    if exp_at is not None:
        print("D2 =", hm.show(D2), " V =", hm.show(V), " wrappers:", [hm.show(w) for w in ws])
        for l in lines[:14]: print("   ", l)
        shown += 1
        if shown >= 3: break
    hm.truncate(M0)
