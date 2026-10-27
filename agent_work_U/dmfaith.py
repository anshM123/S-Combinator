"""Faithfulness check of the DM model: run genuine leftmost-outermost reduction on the whole term (tree form, one redex
per step) and verify that the successive leftmost-path states predicted by dm.py (round survivors) appear, in order,
as the subterm at the leftmost-path position currently being reduced.  usage: python dmfaith.py TERM STEPS"""
import sys
sys.setrecursionlimit(100000)
from dm import *
def lo_step(t):
    """leftmost-outermost step on hash-consed term t; returns (new_t, path) or None.  path = list of 0/1 moves (0 = into
    function part, 1 = into argument) to the contracted redex."""
    args, h = spine(t)
    if h == 0 and len(args) >= 3:
        x, y, z = args[0], args[1], args[2]
        new = build(app(app(x, z), app(y, z)), args[3:])
        return new, []
    # not a head redex: try function part then argument part (leftmost first)
    if t <= 0: return None
    r = lo_step(L[t])
    if r is not None: return app(r[0], R[t]), [0] + r[1]
    r = lo_step(R[t])
    if r is not None: return app(L[t], r[0]), [1] + r[1]
    return None
def leftpath_node(t):
    """descend along first components of head normal forms: return the deepest node on the leftmost path that is not
    an hnf (or None)."""
    while True:
        args, h = spine(t)
        if h != 0: return t
        if len(args) >= 3: return t
        if len(args) == 0: return None
        t = args[0]
if __name__ == "__main__":
    t = parse(sys.argv[1]); N = int(sys.argv[2])
    # DM prediction
    rounds = []
    dm_term(t, 100000, rounds=rounds)
    pred = [r for r in rounds]
    # genuine reduction: record the leftmost-path active node after each step
    seen = []; cur = t
    for i in range(N):
        node = leftpath_node(cur)
        if node is None: break
        if not seen or seen[-1] != node: seen.append(node)
        r = lo_step(cur)
        if r is None: break
        cur = r[0]
    # every DM survivor that is not an hnf should appear in 'seen' in order
    ps = [p for p in pred if len(spine(p)[0]) >= 3]
    j = 0; matched = 0
    for p in ps:
        while j < len(seen) and seen[j] != p: j += 1
        if j < len(seen): matched += 1; j += 1
        else: break
    print("DM survivors (non-hnf):", len(ps), " matched in genuine LO run (in order):", matched, " LO steps:", i + 1)
