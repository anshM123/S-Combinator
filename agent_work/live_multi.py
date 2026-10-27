"""Phase-3 traces for LIVE multi-wrapper phase-2 handlers (no p-headed wrapper, outermost wrapper not bare S)."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, p3events as E
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
nshow = int(sys.argv[2]); shown = 0; M0 = hm.mark(); st = collections.Counter()
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3" or hm.R[V] == Y: hm.truncate(M0); continue
    ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    if any(hm.head(w) == P for w in ws) or ws[0] == 0: hm.truncate(M0); continue
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    lst = [Rr, Y, X, D3]; lines = []
    for t in range(60):
        lines.append(hm.show_list(lst, maxn=7)[:180].replace("p", "p'"))
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hm.step(lst)
    h = hm.head(lst[-1]); out = "reexec" if h == C else ("p'-front" if h == P else "call " + hm.NAMES.get(h, "?"))
    st[(len(ws), "outer " + E.cls(ws[0]), out, "steps<=5" if len(lines) <= 6 else "longer")] += 1
    if shown < nshow and len(lines) > 6:
        print("D2 =", hm.show(D2), " V =", hm.show(V))
        for l in lines[:12]: print("   ", l)
        shown += 1
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
