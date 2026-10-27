"""Random multi-phase chains.  Phase-2 data D2 = d1.(...(dk.p)) with random closed wrappers (sizes up to W leaves,
k = 1..K).  Follow every proper transfer (p-headed stuck front, proper right comb over y at position 2 or 3) into the
next phase (V[y -> p, p -> c_j]) up to depth 6; report the maximal number of proper phases and examples."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
def rand_term(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return hm.app(rand_term(k), rand_term(n - k))
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2]); W = int(sys.argv[3]); K = int(sys.argv[4])
    budget = 4000
    M0 = hm.mark()
    depth_count = collections.Counter(); best = []
    for it in range(N):
        k = random.randint(1, K)
        D = P
        for _ in range(k): D = hm.app(rand_term(random.randint(1, W)), D)
        frontier = [(D, 0, [hm.show(D)])]
        maxd = 0
        while frontier:
            Dc, j, path = frontier.pop()
            r, Vs = c3.phase(Dc, budget)
            if r != "proper": 
                maxd = max(maxd, j); continue
            if j + 1 >= 6: maxd = max(maxd, j + 1); continue
            for V in Vs[:2]:
                Dn = tg.subst(tg.subst(V, P, c3.FROZ[j]), Y, P)
                frontier.append((Dn, j + 1, path + [hm.show(Dn)[:80]]))
                maxd = max(maxd, j + 1)
                if j + 1 >= 2 and len(best) < 10: best.append(path + [hm.show(Dn)[:80]])
        depth_count[maxd] += 1
        hm.truncate(M0)
    print("max proper phases (counting phase 2 as the first):", dict(depth_count))
    for b in best[:10]: print(" -> ".join(b))
