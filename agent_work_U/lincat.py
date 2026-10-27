"""Find closed sigma (<= NMAX leaves) whose DM transition on K atom args is 'small':
each atom occurs at most MAXOCC times in the stuck state.  usage: python lincat.py NMAX K MAXOCC"""
import sys
from dm import *
NMAX = int(sys.argv[1]); K = int(sys.argv[2]); MAXOCC = int(sys.argv[3])
xs = [atom("x%d" % (i + 1)) for i in range(K)]
def occ(i, a):
    c = 0; st = [i]
    while st:
        j = st.pop()
        if j == a: c += 1
        elif j > 0: st.append(L[j]); st.append(R[j])
    return c
res = {}
for n in range(1, NMAX + 1):
    m = mark()
    for sg in trees(n):
        t = build(sg, xs)
        r = dm_term(t, 3000)
        if r[0] != "stuck": continue
        st = stuck_term(r)
        if all(occ(st, a) <= MAXOCC for a in xs):
            key = show(st)
            if key not in res: res[key] = (n, show(sg), r[3])
for k, v in sorted(res.items(), key=lambda kv: (len(kv[0]), kv[0])):
    print("%-40s <= %s (%d leaves, %d steps)" % (k, v[1], v[0], v[2]))
print("distinct", len(res))
