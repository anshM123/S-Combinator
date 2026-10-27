"""Do all unique-redex runs follow Theorem UR's Phi-machine? (main agent, 2026-10-26)
Theorem UR's proof: from Phi(c; R) = [c, S c, S c] ++ R with c = S p (S q), the run walks down the left spine of p
(p_i = S p_{i+1} (S q_{i+1})) to a base p_m and returns to Phi(S q_m (S c); R'). This checks, for every unique-redex term
in FILE, whether from some point on every consecutive pair of Phi-elements satisfies c' = S q_m(c) (S c), and records the
bases p_m met (the element where the walk stops). Usage: python ur_walk.py FILE [STEPS]"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from ur_phi import phi_elements

def form(c):
    """(p, q) if c = S p (S q), else None"""
    args, h = hc.spine(c)
    if h != 0 or len(args) != 2: return None
    a2, h2 = hc.spine(args[1])
    if h2 != 0 or len(a2) != 1: return None
    return args[0], a2[0]

def walk(c):
    pq = form(c)
    if pq is None: return None
    p, q = pq
    while form(p) is not None: p, q = form(p)
    return p, q

if __name__ == "__main__":
    path = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 12000
    terms = [l.split()[1] for l in open(path, encoding="utf-8") if len(l.split()) > 2 and l.split()[1].startswith("S")]
    res = collections.Counter(); bases = collections.Counter(); odd = []
    for src in terms:
        ph, ur = phi_elements(src, N)
        cs = [c for n, c in ph]
        start = None
        for i in range(len(cs) - 1):
            w = walk(cs[i])
            ok = w is not None and cs[i + 1] == hc.app(hc.app(0, w[1]), hc.app(0, cs[i]))
            if ok and start is None: start = i
            if not ok: start = None
        good = start is not None and start < len(cs) // 2
        res[(ur, good)] += 1
        if good:
            bs = {hc.show(walk(c)[0]) for c in cs[start:-1]}
            bases[tuple(sorted(bs))] += 1
        else: odd.append(src)
    print(f"{len(terms)} terms; (unique redex for {N} steps, follows c' = S q_m (S c) from some point on): {dict(res)}")
    print("bases p_m met by the walk:", dict(bases))
    for s in odd[:10]: print("  does not follow:", s)
