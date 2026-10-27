import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
M0 = hm.mark(); st = collections.Counter(); shown = 0
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3": hm.truncate(M0); continue
    ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    fh = any(hm.head(w) == P for w in ws)
    fh1 = any(hm.head(w) == 0 and hm.spine(w)[0] and hm.head(hm.spine(w)[0][0]) == P for w in ws)
    if fh or fh1 or ws[0] == 0 or len(ws) == 1: hm.truncate(M0); continue
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    st3 = [Rr, Y, X, D3]; s, k = hm.run(st3, 1500)
    h = hm.head(st3[-1]); out = "reexec" if h == C else ("p'-front" if h == P else "call " + hm.NAMES.get(h, "?"))
    st[(tuple("S" if w == 0 else ("P" if P in tg.atoms(w) else "CL") for w in ws), out, "steps=%d" % min(k, 9))] += 1
    if shown < 6:
        print("D2 =", hm.show(D2), " V =", hm.show(V), " ->", out, "after", k, "steps")
        shown += 1
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
