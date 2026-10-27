"""Agent U round 5: three-slot sawtooth node N_i . N_y . N_z (one SS-nest family, base B0 varied <= MAXB leaves).
Countdown is the SS-iterator; the base decides the reload. Reports node-shape transitions per branch."""
import sys, collections
from agent_u_ctxnest import run, isC, spine
from symb import trees, show
SS = ("S", "S")
def stop(K, br, n):
    h, a = spine(K[0])
    if isC(h) and len(a) == 2 and isC(a[0]) and isC(a[1]):
        return (h[2:], a[0][2:], a[1][2:])
    return None
if __name__ == "__main__":
    MAXB = int(sys.argv[1])
    cnt = collections.Counter(); hits = []
    for nb in range(1, MAXB + 1):
        for B0 in trees(nb):
            fams = [((SS, "#"), B0)]
            node = ((("C", 0, "i", 0), ("C", 0, "y", 0)), ("C", 0, "z", 0))
            out = run([node, "w1", "w2"], fams, stop, maxsteps=60, cap=4)
            tr = [o for o in out if isinstance(o[1], tuple) and o[0].get("i") == ("eq", 0)]
            for o in tr: cnt[o[1]] += 1
            if any(o[1][2] != ("z", 0) or (o[1][1][0] == "z") for o in tr):
                hits.append((show(B0), [(o[0], o[1], o[2]) for o in tr]))
    print("reload transitions:", cnt.most_common(12)); print("reloads touching z:", len(hits))
    for h in hits[:12]: print(h)
