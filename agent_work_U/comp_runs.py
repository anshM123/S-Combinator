"""DM runs of component terms: for each n, count terms in {(14,28),(14,26)}, the number of rounds, how runs end,
and print the longest runs with the joint class of every node."""
import sys
from dm import *
from classes import cls, COMPONENT, LFl, MFl
NMAX, SHOW = int(sys.argv[1]), int(sys.argv[2])
def dm_walk(t, maxr=500, bud=200000):
    nodes = [t]; u = t; steps = 0
    while len(nodes) < maxr:
        args, h = spine(u)
        if len(args) == 0: return nodes, "S"
        if len(args) <= 2:
            u = args[0]; nodes.append(u); continue
        if MFl[cls(u)[1]] == 0: return nodes, "bot"
        st = list(reversed(args)); ok = False
        for k in range(bud):
            if len(st) <= 2: ok = True; break
            a = st[-1]; aa, hh = spine(a)
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(aa))
        if not ok: return nodes, "cap"
        u = st[-1]; nodes.append(u)
    return nodes, "long"
for n in range(3, NMAX + 1):
    res = []
    for t in trees(n):
        if cls(t) not in COMPONENT: continue
        nodes, end = dm_walk(t)
        comp = sum(1 for v in nodes if len(spine(v)[0]) >= 3)
        res.append((comp, len(nodes), end, t, nodes))
    res.sort(key=lambda r: -r[0])
    ends = {}
    for r in res: ends[r[2]] = ends.get(r[2], 0) + 1
    print("n=%d component terms %d ends %s max computed %s" % (n, len(res), ends, res[0][0] if res else None))
    if n == NMAX:
        for r in res[:SHOW]:
            print(" ", show(r[3]), "computed", r[0], "end", r[2])
            for v in r[4][:14]: print("     ", cls(v), size(v), show(v, maxlen=90))
