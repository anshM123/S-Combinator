"""R3 agent: exhaustive census of R3 on RIGHT COMBS over p with closed wrappers (one occurrence of p), S-headed,
total size exactly N leaves (chain3.rcombs restricted to size N).  usage: rcomb_census.py N"""
import sys, os, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y = c3.P, c3.Y
def rcombs_exact(N):
    closed = {n: hm.trees(n) for n in range(1, N)}
    out = []
    def rec(t, sz):
        if sz == N: out.append(t); return
        for n in range(1, N - sz + 1):
            for d in closed.get(n, []):
                rec(hm.app(d, t), sz + n)
    rec(P, 1)
    return [t for t in out if t != P]
if __name__ == "__main__":
    N = int(sys.argv[1]); st = collections.Counter(); ex = []
    data = rcombs_exact(N); M0 = hm.mark()
    for D in data:
        if hm.head(D) != 0: continue
        st["data"] += 1
        o2, V, _ = T3.phase(D, 2000)
        if o2 != "proper3": hm.truncate(M0); continue
        st["proper transfers"] += 1
        D3 = tg.subst(tg.subst(V, P, c3.FROZ[0]), Y, P)
        o3, V3, _ = T3.phase(D3, 2000)
        st["next phase " + o3] += 1
        if o3 == "proper3" and len(ex) < 6: ex.append((hm.show(D), hm.show(V), hm.show(V3)))
        hm.truncate(M0)
    for k in sorted(st): print(k, st[k])
    for e in ex: print("R3 VIOLATION on a right comb:", e)
