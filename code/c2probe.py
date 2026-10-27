"""Anatomy of terminating head runs: steps D, openings of original vs compound nodes, spine args pushed.
Uses object identity: original occurrences are distinct objects; b·c compounds are new objects."""
import sys, collections
sys.setrecursionlimit(10000)
from fullread import N, nodes
def build(t):
    if t == "S": return N()
    return N(build(t[0]), build(t[1]))
from symb import trees, show
def run(t, budget):
    root = build(t)
    # spine args of the root
    args = []; a = root
    while a.l is not None: args.append(a.r); a = a.l
    args.reverse()
    st = args[::-1]                 # top at end
    D = 0; orig_open = 0; comp_open = 0; pushed = 0
    while len(st) >= 3:
        if D >= budget: return None
        a = st.pop(); b = st.pop(); c = st.pop()
        if a.orig: orig_open += 1
        else: comp_open += 1
        ch = []
        x = a
        while x.l is not None: ch.append(x.r); x = x.l
        pushed += len(ch)
        st.append(N(b, c, orig=False)); st.append(c)
        st.extend(ch)                # ch collected bottom-up: last spine arg first -> push so first arg ends on top
        D += 1
    return D, orig_open, comp_open, pushed, len(args)
worst = {}
for n in range(4, int(sys.argv[1]) + 1):
    best = None; tot = cnt = 0; cmax = 0
    for t in trees(n):
        r = run(t, 4 * n + 20)
        if r is None: continue
        D, oo, co, pu, l0 = r
        cnt += 1; cmax = max(cmax, co)
        if best is None or D > best[0]: best = (D, oo, co, pu, l0, show(t))
    print(f"n={n:2d} terminating {cnt:6d}  max steps {best[0]:3d} (2n-5={2*n-5})  at {best[5]}: orig-openings {best[1]} "
          f"compound-openings {best[2]} pushed {best[3]}  | max compound openings over all runs {cmax}")
