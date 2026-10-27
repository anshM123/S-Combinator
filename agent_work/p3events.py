"""Phase-3 runs from REAL phase-2 outputs (position-3 proper transfers): which events occur?
  sigC : front in C (contains c, no p/x/y/r), 2nd = the only P-element (P = contains new p, no x/y/r), 3rd = bare y
  PonY : any P-element glued onto the bare y
  ydown: bare y at position 2 under an S-headed front (bare y leaves the Y-top)
  CY   : a C-element glued onto a Y-element
  final: outcome; at p-fronts, what is at position 3 (P / bare y / other)"""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def cls(t):
    a = tg.atoms(t)
    if a.get(X) or a.get(Y) or a.get(Rr): return "Y"
    if a.get(P): return "P"
    if a.get(C): return "C"
    return "CL"
def p3(D3, ev, budget=1500):
    st = [Rr, Y, X, D3]
    seen = set()
    for t in range(budget):
        if len(st) < 3: ev["hnf"] += 1; return
        a, b, c = st[-1], st[-2], st[-3]
        if hm.head(a) != 0:
            h = hm.head(a)
            if h == P:
                k = cls(c)
                ev["pfront pos3=" + ("bare-y" if c == Y else k)] += 1
            else: ev["stuck " + hm.NAMES.get(h, "?")] += 1
            for e in seen: ev["EV " + e] += 1
            if not seen: ev["EV none"] += 1
            return
        L = list(reversed(st))
        nP = sum(1 for e in L if cls(e) == "P")
        ca, cb, cc = cls(a), cls(b), cls(c)
        if ca == "C" and cb == "P" and nP == 1 and c == Y: seen.add("sigC")
        if cb == "P" and c == Y: seen.add("PonY")
        if b == Y: seen.add("ydown")
        if cb == "C" and cc == "Y": seen.add("CY")
        hm.step(st)
    ev["budget"] += 1
    for e in seen: ev["EV " + e] += 1
if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "ex":
        N = int(sys.argv[2])
        data = [D for D in c3.rcombs(N) if hm.head(D) == 0]
    else:
        NK, WK, NT = map(int, sys.argv[2:5])
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
        data = [hm.app(K, T) for T in tails if T != P for K in closedK]
    M0 = hm.mark(); tot = collections.Counter(); combo = collections.Counter()
    for D2 in data:
        o2, V, _ = T3.phase(D2, 1500)
        if o2 == "proper3":
            D3 = tg.subst(tg.subst(V, P, C), Y, P)
            ev = collections.Counter()
            p3(D3, ev)
            tot.update(ev)
            # which events happened
            evs = set()
            st = [Rr, Y, X, D3]
            tot["runs"] += 1
        hm.truncate(M0)
    print(tot)
