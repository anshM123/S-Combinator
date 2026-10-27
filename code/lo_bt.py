"""Follow the branch that leftmost-outermost evaluation settles into, via the Böhm tree (main agent).
At each node u: compute hnf(u) with the head machine; the LO evaluation normalises the components left to right, so it
descends into the FIRST component that does not normalise (normalisation tested by a bounded recursive hnf search).
Prints, per level, the number of hnf components, the index LO descends into, the node size and its M35 class.
Usage: python lo_bt.py TERM LEVELS"""
import sys
sys.setrecursionlimit(1000000)
from symb import parse, show, spine, hnf
from verify_model import load
Mr, MF, MT = load("../data/model35_hn.txt"); sM = Mr.index("S")
memo = {}
def cls(t):
    """M35 class; memo keyed by id but storing the object, so a recycled id can never return a stale class"""
    if t == "S": return sM
    k = id(t)
    hit = memo.get(k)
    if hit is not None and hit[0] is t: return hit[1]
    v = int(MT[cls(t[0]), cls(t[1])])
    memo[k] = (t, v)
    return v
def size(t):
    st = [t]; n = 0
    while st:
        x = st.pop()
        if isinstance(x, tuple): st.append(x[0]); st.append(x[1])
        else: n += 1
    return n
def normalises(u, budget=[0], depth=0):
    if depth > 40: return False
    if not MF[cls(u)]: return False                       # no hnf at all (Theorem Q10)
    r = hnf(u, 4000)
    if r[0] != "hnf": return False
    return all(normalises(c, budget, depth + 1) for c in r[1])
if __name__ == "__main__":
    u = parse(sys.argv[1]); L = int(sys.argv[2])
    for lvl in range(L):
        c = cls(u)
        if not MF[c]:
            print(f"level {lvl}: node of size {size(u)} has NO hnf (M35 class {c}) — LO ends in an infinite head run here: {show(u)[:80]}")
            break
        r = hnf(u, 20000)
        comps = r[1]
        idx = None
        for i, x in enumerate(comps):
            if not normalises(x): idx = i; break
        print(f"level {lvl}: size {size(u)}, class {c}, hnf has {len(comps)} components; LO descends into component {idx}")
        if idx is None: print("   all components normalise (finite subtree)"); break
        u = comps[idx]
