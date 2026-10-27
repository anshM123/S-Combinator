"""Full leftmost-outermost reduction with a normal-subterm cache (main agent).
Reports where the LO redex lives over time (argument path from the root) and whether LO settles in one subterm.
Usage: python lo_full.py TERM STEPS"""
import sys
sys.setrecursionlimit(1000000)
from symb import parse, show, spine

NORMAL = set()            # ids of subterms known to be in normal form (immutable tuples, ids stable while alive)
KEEP = []                 # keep references so ids are not reused

def is_normal_cached(u):
    return u == "S" or id(u) in NORMAL

def find(u):
    """return (new_u, path) for the LO redex inside u, or None if u is normal"""
    if is_normal_cached(u): return None
    h, args = spine(u)
    if len(args) >= 3:
        a, b, c = args[0], args[1], args[2]
        new = ((a, c), (b, c))
        for x in args[3:]: new = (new, x)
        return new, ()
    for i, x in enumerate(args):
        r = find(x)
        if r is not None:
            nx, p = r
            nargs = list(args); nargs[i] = nx
            t2 = h
            for y in nargs: t2 = (t2, y)
            return t2, (i,) + p
    NORMAL.add(id(u)); KEEP.append(u)
    return None

if __name__ == "__main__":
    t = parse(sys.argv[1]); STEPS = int(sys.argv[2])
    paths = []
    for step in range(STEPS):
        r = find(t)
        if r is None: print("normal form at step", step); break
        t, p = r; paths.append(p)
    depths = [len(p) for p in paths]
    print(sys.argv[1], "LO steps:", len(paths), "| redex depth every", max(1, len(paths) // 12), "steps:",
          [depths[i] for i in range(0, len(depths), max(1, len(depths) // 12))])
    tail = paths[-min(2000, len(paths)):]
    pre = tail[0]
    for q in tail[1:]:
        k = 0
        while k < min(len(pre), len(q)) and pre[k] == q[k]: k += 1
        pre = pre[:k]
    print("   last", len(tail), "redexes share the argument path", pre, "(depth", len(pre), ")")
    # the subterm LO is working in
    u = t
    for i in pre:
        h, args = spine(u); u = args[i]
    h, args = spine(u)
    print("   that subterm has", len(args), "spine args; first:", show(args[0])[:60] if args else "-")
