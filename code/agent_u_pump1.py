import sys
sys.path.insert(0, r"C:\Users\anshm\Downloads\money problems\code")
from agent_u_sim import app, apps, spine, show
from symb import trees
def conv(t): return 0 if t == "S" else app(conv(t[0]), conv(t[1]))
small = [conv(t) for n in range(1, 6) for t in trees(n)]
res = []
for X0 in small:
    for M in small:
        if M == 0: continue
        ok_all = True; info = []
        for n in range(1, 6):
            st = [0, X0] + [0] * n + [M, conv(("S", "S")), conv((("S", "S"), "S"))]
            hits = []
            for step in range(1, 600):
                if len(st) < 3: break
                a, b, c = st[0], st[1], st[2]
                st = spine(a) + [c, app(b, c)] + st[3:]
                # template [S, X, S^n, M]
                if len(st) >= n + 3 and st[0] == 0 and all(e == 0 for e in st[2:2 + n]) and st[2 + n] == M and step > n + 1:
                    hits.append(step)
                    if len(hits) >= 3: break
            if len(hits) < 2: ok_all = False; break
            info.append((n, hits))
        if ok_all: res.append((show(X0), show(M), info))
print(len(res))
for r in res[:10]: print(r)
