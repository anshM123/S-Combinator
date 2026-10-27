"""Find small hnf-free S-terms whose head run has an eventually periodic TOP WINDOW (shapes of the first 3 list
elements cut at depth 2), i.e. candidate 'cells' whose stage mod p is readable by a bounded pattern.  Report the
preperiod and period of the window sequence (first 3000 steps)."""
import sys
from dm import *
NMAX, STEPS = map(int, sys.argv[1:3])
def shape(i, d):
    if i <= 0: return "S"
    if d == 0: return "*"
    return "(" + shape(L[i], d - 1) + " " + shape(R[i], d - 1) + ")"
res = []
for n in range(4, NMAX + 1):
    for t in trees(n):
        args, h = spine(t)
        if len(args) < 3: continue
        m = mark()
        st = list(reversed(args)); seq = []; ok = True
        for k in range(STEPS):
            if len(st) < 3: ok = False; break
            seq.append((min(len(spine(st[-1])[0]), 3), min(len(spine(st[-2])[0]), 3), min(len(spine(st[-3])[0]), 3)))
            a = st[-1]; aa, hh = spine(a)
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
        truncate(m)
        if not ok: continue
        # find smallest period p <= 50 such that the last 1000 entries are p-periodic
        tail = seq[-1500:]
        for p in range(1, 51):
            if all(tail[i] == tail[i + p] for i in range(len(tail) - p)):
                res.append((p, n, show(t))); break
res.sort()
print("periodic-window cells:", len(res))
for r in res[:15]: print(r)
