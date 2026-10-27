"""R3 agent: exhaustive census of R3 violations.
usage: r3census.py one N      all S-headed ORDERED data G[p], G a 1-hole context with exactly N leaves (one p)
       r3census.py two N      all S-headed ORDERED data with exactly two occurrences of p and <= N leaves
For each proper position-3 phase-2 transfer V, run the next phase of V[y:=p', p:=c] and count proper transfers
(= R3 violations); also record the outcome of the phase after a violation."""
import sys, os, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, phase2_general as pg
P, Y = c3.P, c3.Y
def check(D, st, ex):
    o2, V, _ = T3.phase(D, 2000)
    if o2 != "proper3": return
    st["proper transfers"] += 1
    D3 = tg.subst(tg.subst(V, P, c3.FROZ[0]), Y, P)
    o3, V3, _ = T3.phase(D3, 2000)
    st["next phase " + o3] += 1
    if o3 == "proper3":
        D4 = tg.subst(tg.subst(V3, P, c3.FROZ[1]), Y, P)
        o4, _, _ = T3.phase(D4, 2000)
        st["  violation, then phase 4 " + o4] += 1
        if len(ex) < 10: ex.append((hm.show(D), hm.show(V), hm.show(V3)))
def two_hole(n):
    """all binary trees with n leaves in which exactly two leaves are p (others S)"""
    out = []
    for t in hm.trees(n):
        # enumerate leaf positions by spine traversal
        leaves = []
        def walk(u, path):
            if u <= 0: leaves.append(path); return
            walk(hm.L[u], path + "L"); walk(hm.R[u], path + "R")
        walk(t, "")
        m = len(leaves)
        for i in range(m):
            for j in range(i + 1, m):
                out.append((t, leaves[i], leaves[j]))
    return out
def place(t, paths):
    def rec(u, path):
        if u <= 0: return P if path in paths else u
        return hm.app(rec(hm.L[u], path + "L"), rec(hm.R[u], path + "R"))
    return rec(t, "")
if __name__ == "__main__":
    mode, N = sys.argv[1], int(sys.argv[2])
    st = collections.Counter(); ex = []
    if mode == "one":
        CS = tg.contexts(N); M0 = hm.mark()
        for G in CS:
            D = tg.subst(G, tg.HOLE, P)
            if hm.head(D) != 0 or not pg.ordered(D): hm.truncate(M0); continue
            st["ordered data"] += 1
            check(D, st, ex)
            hm.truncate(M0)
    else:
        for n in range(3, N + 1):
            for (t, a, b) in two_hole(n):
                M0 = hm.mark()
                D = place(t, {a, b})
                if hm.head(D) != 0 or not pg.ordered(D): hm.truncate(M0); continue
                st["ordered data"] += 1
                check(D, st, ex)
                hm.truncate(M0)
    for k in sorted(st): print(k, st[k])
    for e in ex: print("violation: D =", e[0], " V =", e[1], " V3 =", e[2])
