import sys
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, p3events as E
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
shown = 0; M0 = hm.mark()
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3": hm.truncate(M0); continue
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    st = [Rr, Y, X, D3]; lines = []; hit = False
    for t in range(80):
        lines.append(hm.show_list(st, maxn=8)[:200])
        if len(st) < 3 or hm.head(st[-1]) != 0: break
        a, b, c = st[-1], st[-2], st[-3]
        if E.cls(b) == "C" and E.cls(c) == "Y" and hm.head(c) == P: hit = True
        hm.step(st)
    if hit:
        print("D2 =", hm.show(D2), " V =", hm.show(V))
        for l in lines[:16]: print("   ", l.replace("p", "p'"))
        shown += 1
        if shown >= int(sys.argv[2]): break
    hm.truncate(M0)
