"""R3 agent: random search for counterexamples to R3 (ordered datum D, proper position-3 transfer V, next phase
V[y:=p', p:=c] makes a proper position-3 transfer).
usage: r3search.py SEED NMAX COUNT MODE
  MODE = ord1   random S-headed ORDERED data with exactly one occurrence of p (1-hole contexts)
         ord2   random S-headed ORDERED data with exactly two occurrences of p
         rcomb  random right combs over p with closed wrappers (1-3 wrappers), S-headed
Prints counts (transfers, R3 violations, chain lengths) and the first violations found."""
import sys, os, random, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, phase2_general as pg
P, Y = c3.P, c3.Y
def rtree(n, holes):
    leaves = [P] * holes + [0] * (n - holes)
    random.shuffle(leaves)
    def build(lo, hi):
        if hi - lo == 1: return leaves[lo]
        k = random.randint(lo + 1, hi - 1)
        return hm.app(build(lo, k), build(k, hi))
    return build(0, n)
def rclosed(n):
    return rtree(n, 0)
def gen(mode, N):
    if mode in ("ord1", "ord2"):
        n = random.randint(4, N)
        return rtree(n, 1 if mode == "ord1" else 2)
    k = random.randint(1, 3); t = P; budget = N - 1
    for i in range(k):
        m = random.randint(1, max(1, budget // (k - i)))
        t = hm.app(rclosed(m), t); budget -= m
    return t
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2]); M = int(sys.argv[3]); mode = sys.argv[4]
    st = collections.Counter(); M0 = hm.mark(); ex = []
    for it in range(M):
        D = gen(mode, N)
        if hm.head(D) != 0 or (mode != "rcomb" and not pg.ordered(D)):
            hm.truncate(M0); continue
        st["data"] += 1
        o2, V, _ = T3.phase(D, 3000)
        if o2 != "proper3": hm.truncate(M0); continue
        st["proper transfers"] += 1
        D3 = tg.subst(tg.subst(V, P, c3.FROZ[0]), Y, P)
        o3, V3, _ = T3.phase(D3, 3000)
        if o3 == "proper3":
            st["R3 VIOLATIONS"] += 1
            if len(ex) < 6: ex.append((hm.show(D), hm.show(V), hm.show(V3)))
            D4 = tg.subst(tg.subst(V3, P, c3.FROZ[1]), Y, P)
            o4, _, _ = T3.phase(D4, 3000)
            st["  ... and phase 4 " + o4] += 1
        hm.truncate(M0)
    for k in sorted(st): print(k, st[k])
    for e in ex: print("violation: D =", e[0], " V =", e[1], " V3 =", e[2])
