"""Like combhalve.py but reports, for each (q, v), the return map j -> k for returns to [N_k, q', v'] where q', v' may be
ANY elements (we record (k, q' == q, v' == v)).  Prints pairs where some return has k != j + const or depends on parity."""
import sys
from dm import *
NMAX = int(sys.argv[1]); JMAX = int(sys.argv[2]); BUDGET = int(sys.argv[3])
N = [0]
for j in range(1, 400): N.append(app(0, N[-1]))
Nid = {x: k for k, x in enumerate(N)}
cands = []
for n in range(1, NMAX + 1): cands += trees(n)
stats = {"anyret": 0, "pairs": 0}
for q in cands:
    for v in cands:
        stats["pairs"] += 1
        ks = []
        for j in range(JMAX + 1):
            m = mark()
            st = [v, q, N[j]]
            res = None
            for t in range(BUDGET):
                n = len(st)
                if n >= 3:
                    a = st[-1]; args, h = spine(a)
                    st.pop(); b = st.pop(); c = st.pop()
                    st.append(app(b, c)); st.append(c); st.extend(reversed(args))
                elif n >= 1:
                    c = st[-1]; args, h = spine(c); st.clear(); st.extend(reversed(args))
                else:
                    break
                if len(st) >= 3 and st[-1] in Nid and t > 0:
                    res = (Nid[st[-1]], len(st), st[-2] == q and st[-3] == v); break
            ks.append(res)
            truncate(m)
        if any(r is not None for r in ks):
            stats["anyret"] += 1
            vals = [r[0] if r else None for r in ks]
            diffs = set(vals[j] - j for j in range(len(vals)) if vals[j] is not None)
            if len(diffs) > 1:
                print("q=%s v=%s  k=%s" % (show(q), show(v), [(r[0], r[1], int(r[2])) if r else None for r in ks]), flush=True)
print(stats)
