"""Skeletons of phase-2 dirty wrappers.  For right-comb data with closed wrappers (exhaustive <= N leaves) collect
every wrapper w_i of every proper V (positions 2/3 at a p-headed stuck front) and abstract maximal closed subterms
to K.  Print the distinct skeletons of the OUTERMOST dirty wrapper and of all dirty wrappers."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3
P, Y = c3.P, c3.Y
def skel(t):
    if not tg.atoms(t): return "K"
    if t == P: return "p"
    if t <= 0: return hm.show(t)
    l, r = hm.L[t], hm.R[t]
    sl, sr = skel(l), skel(r)
    return sl + ("(" + sr + ")" if len(sr) > 1 else sr)
if __name__ == "__main__":
    N = int(sys.argv[1])
    data = c3.rcombs(N)
    outer = collections.Counter(); allw = collections.Counter(); ex = {}
    M0 = hm.mark()
    for D2 in data:
        r, Vs = c3.phase(D2, 3000)
        if r != "proper": hm.truncate(M0); continue
        for V in Vs:
            ws = []
            t = V
            while t != Y: ws.append(hm.L[t]); t = hm.R[t]
            dirty = [d for d in ws if P in tg.atoms(d)]
            # skeleton of whole wrapper list
            sk = " | ".join(skel(d) for d in ws)
            allw[sk] += 1
            ex.setdefault(sk, (hm.show(D2), hm.show(V)))
        hm.truncate(M0)
    print("distinct wrapper-list skeletons:", len(allw))
    for k, v in allw.most_common(60): print(v, "  ", k, "  e.g.", ex[k])
