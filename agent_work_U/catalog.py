"""Catalogue DM macro-transitions:  sigma x1 ... xk  ==>  stuck state (atom-headed), for closed sigma.
usage: python catalog.py NMAX K BUDGET
Prints, for each distinct 'shape' of result (closed subterms replaced by [c] tags with their text), the smallest sigma."""
import sys
from dm import *

NMAX = int(sys.argv[1]); K = int(sys.argv[2]); BUDGET = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
xs = [atom("x%d" % (i + 1)) for i in range(K)]

def closed(i):
    # true if no atom inside
    st = [i]
    while st:
        j = st.pop()
        if j < 0: return False
        if j > 0: st.append(L[j]); st.append(R[j])
    return True

def shape(i):
    """show with closed subterms abbreviated if large"""
    return show(i, maxlen=200)

res = {}
count = {"stuck": 0, "end": 0, "budget": 0}
for n in range(1, NMAX + 1):
    for sg in trees(n):
        t = build(sg, xs)
        r = dm_term(t, BUDGET)
        count[r[0]] += 1
        if r[0] != "stuck": continue
        st = stuck_term(r)
        key = shape(st)
        if key not in res:
            res[key] = (n, show(sg), r[3])
print("counts", count)
items = sorted(res.items(), key=lambda kv: (len(kv[0]), kv[0]))
for k, (n, s, steps) in items:
    print("%-60s  <= %s (%d leaves, %d steps)" % (k, s, n, steps))
print("distinct", len(res))
