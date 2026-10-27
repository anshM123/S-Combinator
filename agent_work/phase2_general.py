"""Phase chains from GENERAL ordered phase-2 data (any 1-hole context G[p] <= N leaves that is ordered and S-headed,
not only right combs).  Count proper phase-2 and proper phase-3 transfers."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3
P, Y = c3.P, c3.Y
def ordered(t):
    stack = [t]
    while stack:
        s = stack.pop()
        if s <= 0 or not tg.atoms(s): continue
        a, h = hm.spine(s)
        if h == 0:
            seen = False
            for x in a:
                if tg.atoms(x): seen = True
                elif seen: return False
        stack.extend(a)
    return True
if __name__ == "__main__":
    N = int(sys.argv[1]); stats = collections.Counter(); ex = []
    for n in range(2, N + 1):
        CS = tg.contexts(n); M0 = hm.mark()
        for G in CS:
            D = tg.subst(G, tg.HOLE, P)
            if hm.head(D) != 0 or not ordered(D): continue
            stats["ordered data"] += 1
            r, Vs = c3.phase(D, 3000)
            if r != "proper": hm.truncate(M0); continue
            stats["proper2"] += 1
            for V in Vs:
                D3 = tg.subst(tg.subst(V, P, c3.FROZ[0]), Y, P)
                r3, V3 = c3.phase(D3, 3000)
                stats["phase3 " + r3] += 1
                if r3 == "proper" and len(ex) < 10: ex.append((hm.show(D), hm.show(V), hm.show(D3), [hm.show(v) for v in V3]))
            hm.truncate(M0)
    print(stats)
    for e in ex: print(e)
