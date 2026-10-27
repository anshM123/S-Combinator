"""S1 agent: trace the phase-2 run of a datum D (string) with class labels CL/P/Y per element.
Marks the single wrapper w = b0.c0 of the transfer's handler (if any), c0, b0, w.y and chain elements E_k.
usage: trace.py "S(SS)S(SS)(S(Sp))" [maxsteps]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import hm, transfer_graph as tg, chain3 as c3
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
def cls(t):
    a = tg.atoms(t)
    if a.get(X, 0) or a.get(Y, 0) or a.get(Rr, 0): return "Y"
    if a.get(P, 0): return "P"
    return "C"
def phase2(D, budget=3000):
    st = [Rr, Y, X, D]; hist = [list(st)]
    for t in range(budget):
        if len(st) < 3 or hm.head(st[-1]) != 0: break
        hm.step(st); hist.append(list(st))
    return hist
def main():
    D = hm.parse(sys.argv[1]); maxs = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    hist = phase2(D)
    last = hist[-1]
    names = {}
    if len(last) >= 3 and hm.head(last[-1]) == P:
        V = last[-3]
        print("transfer: pos3 =", hm.show(V))
        if V > 0 and hm.R[V] == Y and hm.L[V] > 0:
            w = hm.L[V]; b0, c0 = hm.L[w], hm.R[w]
            names = {w: "w", c0: "c0", b0: "b0", V: "w.y"}
            ch = [c0, w]
            for k in range(8): ch.append(hm.app(ch[-2], ch[-1]))
            for k, e in enumerate(ch):
                if e not in names: names[e] = "E%d" % k
            print("w =", hm.show(w), " b0 =", hm.show(b0), " c0 =", hm.show(c0))
    for t, st in enumerate(hist[:maxs]):
        items = []
        for e in reversed(st):
            s = names.get(e, hm.show(e))
            if len(s) > 40: s = s[:37] + "..."
            items.append(cls(e) + ":" + s)
        print(t, "[" + ", ".join(items) + "]")
main()
