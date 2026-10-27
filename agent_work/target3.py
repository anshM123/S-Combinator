"""Targeted test of 'phase 3 is never a proper transfer' beyond the exhaustive range: D2 = K.T with K closed
(<= NK leaves) and T a right comb over p with small closed wrappers (<= WK leaves each, total <= NT leaves).
Phase 2 must end at a p-headed front with a PROPER right comb over y at POSITION 3 (y once, no x, r, wrappers
y-free); then D3 = V[y:=p, p:=c] (p reused as the new live atom) and phase 3 is checked the same way."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, p3shape_pos3 as S3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def phase(D, budget):
    st = [Rr, Y, X, D]
    s, k = hm.run(st, budget)
    if s != "stuck": return s, None, st
    h = hm.head(st[-1])
    if h == P:
        if len(st) >= 3 and S3.proper(st[-3]): return "proper3", st[-3], st
        return "pfront", None, st
    if h == C: return "reexec", None, st
    return "front-" + hm.NAMES.get(h, "?"), None, st
if __name__ == "__main__":
    NK, WK, NT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    closedK = [t for n in range(1, NK + 1) for t in hm.trees(n) if hm.head(t) == 0]
    wr = [t for n in range(1, WK + 1) for t in hm.trees(n)]
    tails = [P]; fr = [(P, 1)]
    while fr:
        nf = []
        for t, sz in fr:
            for d in wr:
                if sz + hm.size(d) <= NT:
                    u = hm.app(d, t); tails.append(u); nf.append((u, sz + hm.size(d)))
        fr = nf
    tails = [t for t in tails if t != P]
    M0 = hm.mark(); st = collections.Counter(); hits = []
    print(len(closedK), "K x", len(tails), "tails", flush=True)
    for T in tails:
        for K in closedK:
            D2 = hm.app(K, T)
            o2, V, _ = phase(D2, 1500)
            st["p2 " + o2] += 1
            if o2 == "proper3":
                D3 = tg.subst(tg.subst(V, P, C), Y, P)
                o3, V3, l3 = phase(D3, 1500)
                st["p3 " + o3] += 1
                if o3 == "proper3" and len(hits) < 10:
                    hits.append((hm.show(D2), hm.show(V), hm.show_list(l3, maxn=5)[:150]))
            hm.truncate(M0)
    print(st)
    for h in hits: print("HIT", h)
