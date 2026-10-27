"""Real single-wrapper phase-2 transfers, w = b0.c0 with b0 != S (pattern alpha) or pattern beta: phase-3 events.
  C0 = number of C-elements in the first phase-3 list; buffer = a C-element glued onto a P'-element; sigC; outcome."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, p3events as E
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark()
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3" or hm.R[V] != Y: hm.truncate(M0); continue
    w = hm.L[V]
    if hm.head(w) != 0: st["PH"] += 1; hm.truncate(M0); continue
    b0 = hm.L[w]
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    lst = [Rr, Y, X, D3]; hm.step(lst)
    L = list(reversed(lst)); C0 = [E.cls(e) for e in L].count("C"); CL0 = [E.cls(e) for e in L].count("CL")
    buf = sig = False
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        L = list(reversed(lst)); cl = [E.cls(e) for e in L]
        if cl[1] == "C" and cl[2] == "P": buf = True
        if cl[0] == "C" and cl[1] == "P" and cl.count("P") == 1 and L[2] == Y: sig = True
        hm.step(lst)
    h = hm.head(lst[-1]) if len(lst) else None
    out = "reexec" if h == C else ("p'-front" if h == P else "other")
    st[("b0=S" if b0 == 0 else "b0!=S", "C0=%d" % min(C0, 3), "CLabove" if CL0 else "noCL", "buf" if buf else "-", "sigC" if sig else "-", out)] += 1
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
