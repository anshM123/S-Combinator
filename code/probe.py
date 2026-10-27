"""Probe experiment: does head reduction of t z1 z2 (z1, z2 opaque variables) track the leftmost Böhm-tree path of t?

Head machine with variables: an element whose head is a variable is 'stuck'; a configuration whose first element is
stuck is a (variable-headed) head normal form. For every closed term we classify its leftmost path
(INF = not finished within the depth cap with every node head-normalising, S = ends at the leaf S, BOT = ends at a
node without hnf (M35 class bottom, Theorem A)) and whether t z1 z2 head-normalises within a step budget.
Usage: python probe.py NMAX
"""
import sys, collections
from verify_model import load
from symb import trees, show, spine

Mm = load("../data/model35_hn.txt"); sM = Mm[0].index("S")
L = load("../data/model36_leftpath.txt"); sL = L[0].index("S")
def mclass(t, memo):
    if t == "S": return sM
    r = memo.get(id(t))
    if r is None:
        r = int(Mm[2][mclass(t[0], memo), mclass(t[1], memo)]); memo[id(t)] = r
    return r
def lclass(t, memo):
    if t == "S": return sL
    r = memo.get(id(t))
    if r is None:
        r = int(L[2][lclass(t[0], memo), lclass(t[1], memo)]); memo[id(t)] = r
    return r

def hnf(t, budget):
    """head machine with variables; returns ('S', comps) | ('var',) | None (budget)"""
    h, args = spine(t)
    if h != "S":
        return ("var",)
    K = list(args); n = 0
    while len(K) >= 3:
        if n >= budget: return None
        a, b, c = K[0], K[1], K[2]
        ha, aa = spine(a)
        if ha != "S":
            return ("var",)                     # a variable reached head position: stuck = hnf
        K = list(aa) + [c, (b, c)] + K[3:]; n += 1
    return ("S", K)

def leftmost(t, cap=60, budget=4000):
    u = t
    for _ in range(cap):
        if not Mm[1][mclass(u, {})]: return "BOT"
        r = hnf(u, budget)
        if r is None: return "BUDGET"
        comps = r[1]
        if not comps: return "S"
        u = comps[0]
    return "INF"

if __name__ == "__main__":
    for n in range(3, int(sys.argv[1]) + 1):
        tab = collections.Counter(); ex = {}
        for t in trees(n):
            lp = leftmost(t)
            pr = hnf((((t, "z1"), "z2")), 20000)
            key = (lp, "probe-hnf" if pr is not None else "probe-diverges", int(L[1][lclass(t, {})]))
            tab[key] += 1
            ex.setdefault(key, show(t))
        print(f"n={n}: (leftmost path, probe, L36 flag) -> {dict(sorted(tab.items()))}", flush=True)
        odd = {k: v for k, v in ex.items() if (k[0] == "S" and k[1] == "probe-diverges") or (k[0] == "INF" and k[1] == "probe-hnf")}
        if odd: print("   unexpected:", odd)
