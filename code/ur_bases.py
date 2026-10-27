"""Which bases exist for unique-redex Φ-machines? (main agent, 2026-10-26)
For every normal form β (not of the form S p (S q)) with up to NMAX leaves, run the head machine on
[β, S x, S y] ++ junk with opaque normal forms x, y, keeping a unique redex (second element of spine ≤ 1, x and y never
opened nor alone in second position, junk never read), until the first Φ-state [g, S g, S g]. Report the return
patterns g(x, y) found, i.e. the possible base behaviours of Theorems UR-Φ / UR-Φ-II and of any further variant.
Usage: python ur_bases.py NMAX"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from li_explore import has_redex, terms
from ur_walk import form

X, Y = -1, -2
JUNK = [-99, -98, -97, -96]

def show(t):
    if t == X: return "x"
    if t == Y: return "y"
    if t == 0: return "S"
    f, a = hc.L[t], hc.R[t]
    s = show(a)
    return show(f) + (s if a <= 0 else "(" + s + ")")

def base_run(beta, cap=300):
    stk = ([beta, hc.app(0, X), hc.app(0, Y)] + JUNK)[::-1]; ops = []
    for n in range(cap):
        c, b2, b3 = stk[-1], stk[-2], stk[-3]
        if n > 0 and b2 == hc.app(0, c) and b3 == b2: return c, "".join(map(str, ops))
        if any(e in JUNK for e in (stk[-1], stk[-2], stk[-3])): return "reads below", None
        bargs, bh = hc.spine(b2)
        if bh != 0 or len(bargs) >= 2: return "second redex or unknown", None
        args, h = hc.spine(stk[-1])
        if h != 0: return "opens x or y", None
        a = stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(args)); ops.append(len(args))
    return "no Phi-state", None

if __name__ == "__main__":
    NMAX = int(sys.argv[1])
    pats = collections.Counter(); examples = {}; fails = collections.Counter(); total = 0
    for n in range(1, NMAX + 1):
        for t in terms(n):
            if has_redex(t) or form(t) is not None: continue
            total += 1
            g, w = base_run(t)
            if isinstance(g, str): fails[g] += 1; continue
            key = show(g)
            pats[key] += 1
            if key not in examples or n < examples[key][0]: examples[key] = (n, hc.show(t), w)
        print(f"<= {n} leaves: {total} normal forms (not S p (S q)); bases found: {sum(pats.values())}", flush=True)
    print("return patterns g(x, y) (count, smallest base, its word):")
    for k, v in pats.most_common(): print(f"  {v:6d}  g = {k:28s}  e.g. {examples[k][1]} ({examples[k][0]} leaves, word {examples[k][2]})")
    print("failures:", dict(fails))
