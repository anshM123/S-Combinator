"""print phase-3 traces (from real phase-2 outputs) in which sigma_C occurs; show the first few lists after it"""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, p3events as E
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
N = int(sys.argv[1]); nshow = int(sys.argv[2])
data = [D for D in c3.rcombs(N) if hm.head(D) == 0]
shown = 0
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3": continue
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    st = [Rr, Y, X, D3]; lines = []; sig = False; ydn = False
    for t in range(60):
        if len(st) < 3 or hm.head(st[-1]) != 0: break
        a, b, c = st[-1], st[-2], st[-3]
        L = list(reversed(st)); nP = sum(1 for e in L if E.cls(e) == "P")
        if E.cls(a) == "C" and E.cls(b) == "P" and nP == 1 and c == Y: sig = True
        if sig and b == Y: ydn = True
        lines.append(hm.show_list(st, maxn=7)[:170])
        hm.step(st)
    lines.append(hm.show_list(st, maxn=7)[:170])
    if sig and ydn:
        print("D2 =", hm.show(D2), " V =", hm.show(V), " D3 =", hm.show(D3).replace("p", "p'"))
        for l in lines[:14]: print("   ", l)
        shown += 1
        if shown >= nshow: break
