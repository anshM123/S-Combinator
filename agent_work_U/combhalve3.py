"""DM runs of [D_n, q, v] (D_n = n nested S over S).  At every DESCENT (round end), if the new list is [D_k, q', v'] for a
comb D_k, record (k, q', v').  For each (q,v) and n, take the first such record after the start.  Report (q,v) for which
the map n -> k is defined for all n in [NLO, NHI], the pair (q',v') takes at most 2 values, and k - n is not constant
(on each parity class).   usage: python combhalve3.py NMAX NLO NHI BUDGET"""
import sys
from dm import *
NMAX, NLO, NHI, BUDGET = map(int, sys.argv[1:5])
D = [0]
for j in range(1, 600): D.append(app(0, D[-1]))
Did = {x: k for k, x in enumerate(D)}
cands = []
for n in range(1, NMAX + 1): cands += trees(n)
nint = 0
for q in cands:
    for v in cands:
        recs = []
        for n in range(NLO, NHI + 1):
            m = mark()
            st = [v, q, D[n]]
            rec = None
            for t in range(BUDGET):
                L_ = len(st)
                if L_ >= 3:
                    a = st[-1]; args, h = spine(a)
                    st.pop(); b = st.pop(); c = st.pop()
                    st.append(app(b, c)); st.append(c); st.extend(reversed(args))
                elif L_ >= 1:
                    c = st[-1]; args, h = spine(c); st.clear(); st.extend(reversed(args))
                    if len(st) == 3 and st[-1] in Did:
                        rec = (Did[st[-1]], st[-2], st[-3], t); break
                else:
                    break
            recs.append(rec)
            if rec is None:
                truncate(m); break
            # keep q', v' ids alive: do not truncate (they are needed for comparison); small anyway
        if len(recs) < NHI - NLO + 1 or any(r is None for r in recs): continue
        pairs = set((r[1], r[2]) for r in recs)
        if len(pairs) > 2: continue
        ks = [r[0] for r in recs]
        ev = set(ks[i] - (NLO + i) for i in range(len(ks)) if (NLO + i) % 2 == 0)
        od = set(ks[i] - (NLO + i) for i in range(len(ks)) if (NLO + i) % 2 == 1)
        if len(ev) <= 1 and len(od) <= 1: continue
        nint += 1
        print("q=%s v=%s ks=%s pairs=%s" % (show(q), show(v), ks, [(show(a), show(b)) for a, b in pairs]), flush=True)
print("interesting", nint)
