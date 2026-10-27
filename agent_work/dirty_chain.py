"""Dirty transfer chains.  A phase: datum D with hole for the predecessor (atom 'p') and possibly frozen opaque atoms
(c1, c2, ...).  Generic run [D[p], x, y, r]; if stuck at a bare p front whose v-input V contains y exactly once and no
x, r (V may contain p and frozen atoms), the next phase's datum is V with y -> new hole and every p -> a new frozen
atom.  Count chains with >= 2 proper (V != y) phases."""
import sys, collections
import hm, transfer_graph as tg
P = hm.atom("p"); X = hm.atom("x"); Y = hm.atom("y"); R = hm.atom("r")
HOLE = tg.HOLE
_fz = {}
def frozen(i):
    if i not in _fz: _fz[i] = hm.atom("c%d" % i)
    return _fz[i]
def phase(D, depth):
    """D: term with HOLE.  returns ('ok', next D) / reason"""
    Dp = tg.subst(D, HOLE, P)
    if hm.head(Dp) != 0: return ("headless", None)
    st = [R, Y, X, Dp]
    s, k = hm.run(st, 3000)
    if s != "stuck": return (s, None)
    f = st[-1]
    if f != P: return ("front", None)
    if len(st) < 3: return ("short", None)
    V = st[-3]
    a = tg.atoms(V)
    if a.get(Y, 0) != 1 or a.get(X, 0) or a.get(R, 0): return ("dirtyx", None)
    if V == Y: return ("identity", None)
    nxt = tg.subst(tg.subst(V, P, frozen(depth)), Y, HOLE)
    return ("ok", nxt)
if __name__ == "__main__":
    smax = int(sys.argv[1])
    stats = collections.Counter(); chains = []
    for n in range(2, smax + 1):
        for G in tg.contexts(n):
            D = G; chain = [hm.show(G)]
            for depth in range(4):
                r, nxt = phase(D, depth)
                if r != "ok": chain.append("[" + r + "]"); break
                chain.append(hm.show(nxt)); D = nxt
            proper = sum(1 for c in chain[1:] if not c.startswith("["))
            stats[proper] += 1
            if proper >= 2: chains.append(chain)
    print(stats)
    for c in chains[:30]: print(" -> ".join(c))
