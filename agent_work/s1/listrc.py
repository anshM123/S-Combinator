import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover6 as C6, multi as MU
hm, c3 = C6.hm, C6.c3
N = int(sys.argv[1]); st = collections.Counter(); ex = {}
for D in c3.rcombs(N):
    if hm.head(D) != 0: continue
    r = C6.classify(D)
    if r is not None and r[0] in ("NHALL", "multi-other"):
        k = (r[0],) + MU.info(D)
        st[k] += 1
        if k not in ex: ex[k] = hm.show(D)
    MU._cl.clear()
for k, v in sorted(st.items(), key=lambda kv: -kv[1]): print(v, ex[k], k)
