"""Hypothesis H3: in phase 3 (datum D3 = V[y := p', p := c] from a proper phase-2 transfer of multi-level data),
no step glues a P'-element (contains p', no x, y, r) onto a Y-element (contains x, y or r) before the run is stuck.
Also record what the glued P'-elements look like if it happens."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
C = c3.FROZ[0]
def cls(t):
    a = tg.atoms(t)
    if a.get(X) or a.get(Y) or a.get(Rr): return "Y"
    if a.get(P): return "P"
    if a.get(C): return "C"
    return "CL"
if __name__ == "__main__":
    N = int(sys.argv[1]); st = collections.Counter(); ex = []
    data = [D for D in c3.rcombs(N) if hm.R[D] != P]
    M0 = hm.mark()
    for D in data:
        r, Vs = c3.phase(D, 4000)
        if r != "proper": hm.truncate(M0); continue
        for V in Vs:
            D3 = tg.subst(tg.subst(V, P, C), Y, P)
            lst = [Rr, Y, X, D3]
            glued = False
            for s in range(4000):
                if len(lst) < 3: break
                a, b, c = lst[-1], lst[-2], lst[-3]
                if hm.head(a) != 0: break
                if cls(b) == "P" and cls(c) == "Y":
                    glued = True
                    if len(ex) < 8: ex.append((hm.show(D), hm.show(D3)[:50], s, hm.show(b)[:40], hm.show(c)[:30]))
                    break
                hm.step(lst)
            st["glue P'->Y" if glued else "no glue"] += 1
        hm.truncate(M0)
    print(st)
    for e in ex: print(e)
