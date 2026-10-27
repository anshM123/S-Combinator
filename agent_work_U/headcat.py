"""For closed sigma <= NMAX leaves and K atom args, list distinct stuck states whose HEAD atom is x_H,
sorted by size.  usage: python headcat.py NMAX K H [LIMIT]"""
import sys
from dm import *
NMAX = int(sys.argv[1]); K = int(sys.argv[2]); H = int(sys.argv[3]); LIMIT = int(sys.argv[4]) if len(sys.argv) > 4 else 60
xs = [atom("x%d" % (i + 1)) for i in range(K)]
res = {}
for n in range(1, NMAX + 1):
    for sg in trees(n):
        t = build(sg, xs)
        r = dm_term(t, 3000)
        if r[0] != "stuck" or r[1] != xs[H - 1]: continue
        st = stuck_term(r)
        key = show(st)
        if key not in res: res[key] = (n, show(sg), r[3], size(st))
items = sorted(res.items(), key=lambda kv: (kv[1][3], kv[0]))
for k, v in items[:LIMIT]:
    print("%-50s <= %s (%d leaves, %d steps)" % (k, v[1], v[0], v[2]))
print("distinct", len(res))
