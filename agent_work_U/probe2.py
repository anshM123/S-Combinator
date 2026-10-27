"""Search closed sigma <= NMAX leaves whose DM run on sigma.x gets stuck at  x (c1 x) (c2 x)  with c1, c2 closed and
c1 != c2 (two independent closed continuations, each holding the datum once).  Also report  x (c1 x) (c2 x) R..."""
import sys
from dm import *
NMAX, BUD = map(int, sys.argv[1:3])
X = atom("x")
def closed(i):
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True
found = {}
for n in range(1, NMAX + 1):
    m = mark()
    for sg in trees(n):
        r = dm_term(app(sg, X), BUD)
        if r[0] != "stuck" or r[1] != X: continue
        args = r[2]
        if len(args) < 2: continue
        ok = True; cs = []
        for a in args[:2]:
            if a > 0 and R[a] == X and closed(L[a]): cs.append(L[a])
            else: ok = False; break
        if ok and cs[0] != cs[1]:
            key = (show(cs[0]), show(cs[1]), len(args))
            if key not in found:
                found[key] = show(sg); print(key, "<=", show(sg), flush=True)
    # keep table (needed for printing) ; memory is fine for <= 11
print("found", len(found))
