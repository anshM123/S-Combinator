"""(C) concrete scan: S-nest countdown with Fibonacci body [S N, t1, t2] -> [N, t2, t1 t2]; does the base B0 reload
an S-nest?  Start [S^(j) B0, Q, V]; report later configurations [S^(m) B0, Q, V, ...] (exact equality of the top 3)."""
import sys
sys.path.insert(0, r"C:\Users\anshm\Downloads\money problems\code")
from agent_u_sim import app, apps, spine, run, show
from symb import trees
def conv(t):
    return 0 if t == "S" else app(conv(t[0]), conv(t[1]))
def nestS(j, b):
    for _ in range(j): b = app(0, b)
    return b
res = []
Bs = [conv(t) for n in range(1, 7) for t in trees(n)]
cs = [conv(t) for n in range(1, 4) for t in trees(n)]
for B0 in Bs:
    nests = {nestS(m, B0): m for m in range(0, 40)}
    for Q in cs:
        for V in cs:
            seqs = []
            for j in range(1, 5):
                st = [nestS(j, B0), Q, V]; hits = []
                for n in range(1, 400):
                    if len(st) < 3: break
                    a, b, c = st[0], st[1], st[2]
                    st = spine(a) + [c, app(b, c)] + st[3:]
                    if st[0] in nests and len(st) >= 3 and st[1] == Q and st[2] == V and n > j:
                        hits.append((n, nests[st[0]]))
                        if len(hits) >= 3: break
                seqs.append(hits)
            if all(s for s in seqs):
                res.append((show(B0), show(Q), show(V), seqs))
print(len(res))
for r in res[:20]: print(r)
