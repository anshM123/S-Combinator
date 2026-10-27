"""Agent U round 5: sawtooth node N_i . N_k . F_m with a third counter F (context ctxF, base bF) in the fuel slot.
Exact symbolic search (agent_u_ctxnest); reports all node-shape transitions (di, dk, dm) per branch."""
import sys, collections
from agent_u_ctxnest import run, isC, spine
from symb import trees, show
SS = ("S", "S"); B = (("S", SS), SS)
def contexts(maxn):
    out = []
    def holes(t):
        if t == "S": yield "#"; return
        for l in holes(t[0]): yield (l, t[1])
        for r in holes(t[1]): yield (t[0], r)
    for n in range(2, maxn + 1):
        for t in trees(n): out.extend(holes(t))
    return out
def node_stop(K, br, n):
    h, a = spine(K[0])
    if isC(h) and h[1] == 0 and len(a) == 2 and isC(a[0]) and a[0][1] == 0 and isC(a[1]) and a[1][1] == 1:
        return (h[2:], a[0][2:], a[1][2:])
    return None
if __name__ == "__main__":
    maxc = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    cnt = collections.Counter(); interesting = []
    for ctxF in contexts(maxc):
        for bF in [t for n in range(1, 4) for t in trees(n)]:
            fams = [((SS, "#"), B), (ctxF, bF)]
            node = ((("C", 0, "i", 0), ("C", 0, "k", 0)), ("C", 1, "m", 0))
            out = run([node, "w1", "w2"], fams, node_stop, maxsteps=60, cap=4)
            trans = [o for o in out if isinstance(o[1], tuple)]
            for o in trans:
                key = tuple((v, d) for v, d in o[1])
                cnt[key] += 1
            # interesting: some transition changes m, or a re-entry from i = 0 to a node with i-slot >= 1
            if any(o[1][2] != ("m", 0) for o in trans) or any(o[0].get("i") == ("eq", 0) for o in trans):
                interesting.append((ctxF, show(bF), [(o[0], o[1], o[2]) for o in trans], len(out)))
    print(cnt.most_common(15))
    print("interesting:", len(interesting))
    for x in interesting[:15]: print(x)
