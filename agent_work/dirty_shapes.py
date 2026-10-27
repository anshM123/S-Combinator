"""Shapes of dirty wrappers.  For a phase datum D (hole p; frozen atoms allowed; no x, y, r) run [D, x, y, r]
generically; at a stuck p-headed front, look at the elements at positions 2 and 3; for every one that is a proper
right comb over y (y once, no x, r) record the class of each wrapper d_i (outermost first):
  'C' closed, 'F' free of p but containing frozen atoms, 'P' p-headed, 'Q' S-headed containing p, 'R' other-atom-headed."""
import sys, collections
import hm, transfer_graph as tg
P = hm.atom("p"); X = hm.atom("x"); Y = hm.atom("y"); Rr = hm.atom("r")
def occ(t, a):
    if t == a: return 1
    if t <= 0: return 0
    return occ(hm.L[t], a) + occ(hm.R[t], a)
def is_closed(t): return not tg.atoms(t)
def wrappers(V):
    ws = []
    while V != Y:
        if V <= 0: return None
        ws.append(hm.L[V]); V = hm.R[V]
    return ws
def wclass(d):
    at = tg.atoms(d)
    if not at: return "C"
    if P not in at: return "F"
    h = hm.head(d)
    if h == P: return "P"
    if h == 0: return "Q"
    return "R"
def analyse(D, budget=3000):
    st = [Rr, Y, X, D]
    s, k = hm.run(st, budget)
    if s != "stuck": return None
    f = st[-1]
    if hm.head(f) != P: return ("front-" + ("frozen" if hm.head(f) not in (X, Y, Rr) else hm.show(hm.head(f))),)
    out = []
    for pos in (2, 3):
        if len(st) < pos: continue
        V = st[-pos]
        a = tg.atoms(V)
        if a.get(Y, 0) != 1 or a.get(X, 0) or a.get(Rr, 0) or V == Y: continue
        ws = wrappers(V)
        if ws is None: continue
        out.append((pos, "".join(wclass(d) for d in ws), "bare" if f == P else "pw"))
    return ("p-front", tuple(out))
if __name__ == "__main__":
    smax = int(sys.argv[1])
    stats = collections.Counter(); ex = {}
    for n in range(2, smax + 1):
        for G in tg.contexts(n):
            D = tg.subst(G, tg.HOLE, P)
            if hm.head(D) != 0: continue
            # classify datum: right comb with closed wrappers?
            ws = []; t = D; rc = True
            while t != P:
                if t <= 0: rc = False; break
                if tg.atoms(hm.L[t]): rc = False; break
                t = hm.R[t]
            kind = "rcomb" if rc else "other"
            r = analyse(D)
            if r is None: stats[(kind, "nostuck")] += 1; continue
            if r[0] != "p-front": stats[(kind, r[0])] += 1; continue
            if not r[1]: stats[(kind, "p-front no proper V")] += 1; continue
            for pos, shape, fr in r[1]:
                key = (kind, pos, shape, fr)
                stats[key] += 1
                ex.setdefault(key, hm.show(D))
    for k, v in sorted(stats.items(), key=lambda kv: str(kv[0])): print(v, k, ex.get(k, ""))
