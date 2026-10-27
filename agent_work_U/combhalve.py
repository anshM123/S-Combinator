"""DM runs of S.N_j.q.v (comb N_j = j-fold S(...(S S)) i.e. N_0 = S, N_{j+1} = S N_j) for closed q, v.
Looks for return to a state [N_k, q, v] (list form) and records k = f(j).  usage: python combhalve.py NMAX JMAX BUDGET"""
import sys
from dm import *
NMAX = int(sys.argv[1]); JMAX = int(sys.argv[2]); BUDGET = int(sys.argv[3])
N = [0]
for j in range(1, 400): N.append(app(0, N[-1]))
Nid = {x: k for k, x in enumerate(N)}
cands = []
for n in range(1, NMAX + 1): cands += trees(n)
base = mark()
found = 0
for q in cands:
    for v in cands:
        fmap = []
        for j in range(JMAX + 1):
            m = mark()
            st = [v, q, N[j]]           # front at end: list [N_j, q, v]
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
                    res = ("end", t); break
                if len(st) == 3 and st[0] == v and st[1] == q and st[2] in Nid:
                    res = ("ret", Nid[st[2]], t + 1); break
            fmap.append(res)
            truncate(m)
        ks = [r[1] if (r and r[0] == "ret") else None for r in fmap]
        if sum(1 for k in ks if k is not None) >= JMAX // 2:
            # interesting if not of the form k = j + c
            diffs = set(k - j for j, k in enumerate(ks) if k is not None)
            if len(diffs) > 1:
                found += 1
                print("q=%s v=%s  f=%s" % (show(q), show(v), ks), flush=True)
print("done, interesting:", found)
