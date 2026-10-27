"""Leftmost Böhm-tree walks inside the resisting component {(14,28), (14,26)} of L36 x M35 (main agent, 2026-10-26).
For every term with <= NMAX leaves in those joint classes: walk u_0 = t, u_{j+1} = first component of hnf(u_j)
(structural step when u_j = S x or S x y; computed step, via the head machine, when u_j has >= 3 arguments). Records the
number of computed steps, how each walk ends (leaf S / node without hnf), and, for the walks with the most computed
steps, the node sequence. Usage: python lw_anatomy.py NMAX [SHOW]"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from li_explore import terms
from verify_model import load

Lr, LF, LT = load("../data/model36_leftpath.txt")
Mr, MF, MT = load("../data/model35_hn.txt")
sL, sM = Lr.index("S"), Mr.index("S")
CL = {}
def cls(i):
    """joint (L36, M35) class of term id i"""
    if i == 0: return (sL, sM)
    r = CL.get(i)
    if r is None:
        a = cls(hc.L[i]); b = cls(hc.R[i])
        r = (int(LT[a[0], b[0]]), int(MT[a[1], b[1]])); CL[i] = r
    return r

def hnf(i, cap=4000):
    """head machine on args(i): returns the final list (length <= 2), or None if no hnf within cap"""
    L = list(hc.spine(i)[0])
    for _ in range(cap):
        if len(L) < 3: return L
        a, b, c = L[0], L[1], L[2]
        L = list(hc.spine(a)[0]) + [c, hc.app(b, c)] + L[3:]
    return None

def walk(t, maxnodes=400):
    nodes = [t]; kinds = []
    u = t
    for _ in range(maxnodes):
        args = hc.spine(u)[0]
        if len(args) == 0: return nodes, kinds, "S"
        if len(args) <= 2:
            u = args[0]; kinds.append("d")
        else:
            if MF[cls(u)[1]] == 0: return nodes, kinds, "bot"
            L = hnf(u)
            if L is None: return nodes, kinds, "cap"
            if len(L) == 0: return nodes, kinds, "S?"
            u = L[0]; kinds.append("c")
        nodes.append(u)
    return nodes, kinds, "long"

if __name__ == "__main__":
    NMAX = int(sys.argv[1]); SHOW = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    target = {(14, 28), (14, 26)}
    for n in range(3, NMAX + 1):
        stats = collections.Counter(); ends = collections.Counter(); best = []
        for t in terms(n):
            if cls(t) not in target: continue
            nodes, kinds, end = walk(t)
            nc = kinds.count("c"); stats[nc] += 1; ends[end] += 1
            best.append((nc, hc.show(t), nodes, kinds, end))
        if not stats: continue
        print(f"{n} leaves: {sum(stats.values())} terms; computed steps per walk {dict(sorted(stats.items()))}; ends {dict(ends)}")
        best.sort(key=lambda x: -x[0])
        for nc, s, nodes, kinds, end in best[:SHOW]:
            print(f"   {nc} computed: {s}  -> {end}")
            for u, k in zip(nodes, kinds + ['.']):
                cl = cls(u)
                print(f"        {k} {cl} |{len(hc.spine(u)[0])} args| {hc.show(u)[:110]}")
