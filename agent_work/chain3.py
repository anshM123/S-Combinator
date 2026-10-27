"""Three-phase chains from right-comb data.  D2 = d1.(d2.(...(dk.p))) with closed wrappers d_i (total leaves <= N).
Phase 2: generic run of [D2, x, y, r]; if stuck at a p-HEADED front (bare p or p.w...) and position 2 or 3 holds a
proper right comb V over y (y once, no x, r), form D3 = V[y -> p, p -> c] and run phase 3 the same way; and so on.
Outcomes per phase: proper / pfront-noV / front-frozen (re-execution) / front-x / front-y / front-r / budget."""
import sys, collections, itertools
import hm, transfer_graph as tg
P = hm.atom("p"); X = hm.atom("x"); Y = hm.atom("y"); Rr = hm.atom("r")
FROZ = [hm.atom("c%d" % i) for i in range(1, 8)]
def subst_atom(t, a, val, memo=None):
    return tg.subst(t, a, val, memo)
def phase(D, budget):
    st = [Rr, Y, X, D]
    s, k = hm.run(st, budget)
    if s != "stuck": return (s, [])
    h = hm.head(st[-1])
    if h == P:
        Vs = []
        for pos in (2, 3):
            if len(st) < pos: continue
            V = st[-pos]
            a = tg.atoms(V)
            if a.get(Y, 0) == 1 and not a.get(X, 0) and not a.get(Rr, 0) and V != Y:
                Vs.append(V)
        return ("proper" if Vs else "pfront-noV", Vs)
    if h in FROZ: return ("front-frozen", [])
    return ("front-" + hm.NAMES.get(h, "?"), [])
def rcombs(N):
    """right combs over p with closed wrappers, total leaves <= N (p counts 1)"""
    closed = [t for n in range(1, N) for t in hm.trees(n)]
    out = [P]
    frontier = [(P, 1)]
    while frontier:
        nf = []
        for t, sz in frontier:
            for d in closed:
                s2 = sz + hm.size(d)
                if s2 <= N:
                    u = hm.app(d, t); out.append(u); nf.append((u, s2))
        frontier = nf
    return [t for t in out if t != P]
if __name__ == "__main__":
    N = int(sys.argv[1]); depth = int(sys.argv[2]) if len(sys.argv) > 2 else 4; budget = 3000
    stats = collections.Counter(); maxproper = 0; examples = collections.defaultdict(list)
    data = rcombs(N)
    print("right-comb data:", len(data))
    M0 = hm.mark()
    for D2 in data:
        # explore all branches (V at pos 2 or 3)
        frontier = [(D2, 0, [hm.show(D2)])]
        while frontier:
            D, j, path = frontier.pop()
            r, Vs = phase(D, budget)
            if r != "proper" or j + 1 >= depth:
                key = (j + (1 if r == "proper" else 0), r)
                stats[key] += 1
                if len(examples[key]) < 3: examples[key].append(" -> ".join(path))
                continue
            for V in Vs:
                Dn = tg.subst(tg.subst(V, P, FROZ[j]), Y, P)
                frontier.append((Dn, j + 1, path + [hm.show(Dn)]))
        if hm.mark() - M0 > 3_000_000:
            pass
    for k, v in sorted(stats.items()): print(v, k, examples[k][:2])
