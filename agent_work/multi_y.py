"""Duplicating transfers: generic run of [D, x, y, r] for ordered data D (right combs over p with closed wrappers, and
general ordered contexts); at a p-headed stuck front, look for elements at positions 2/3 that contain y >= 2 times, no
x, r (p allowed or not).  Report counts and examples; then follow such multi-y values as next-phase data."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
if __name__ == "__main__":
    N = int(sys.argv[1]); stats = collections.Counter(); ex = collections.defaultdict(list)
    for n in range(2, N + 1):
        CS = tg.contexts(n); M0 = hm.mark()
        for G in CS:
            D = tg.subst(G, tg.HOLE, P)
            if hm.head(D) != 0 or not pg.ordered(D): continue
            st = [Rr, Y, X, D]
            s, k = hm.run(st, 3000)
            if s != "stuck" or hm.head(st[-1]) != P: hm.truncate(M0); continue
            for pos in (2, 3):
                if len(st) < pos: continue
                V = st[-pos]; a = tg.atoms(V)
                if a.get(Y, 0) >= 2 and not a.get(X) and not a.get(Rr):
                    key = ("p-free" if not a.get(P) else "with p", pos)
                    stats[key] += 1
                    if len(ex[key]) < 4: ex[key].append((hm.show(D), hm.show(V)[:70]))
            hm.truncate(M0)
    print(stats)
    for k, v in ex.items(): print(k, v)
