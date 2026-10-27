import sys
sys.path.insert(0, r"C:\Users\anshm\Downloads\money problems\code")
from agent_u_sim import app, spine, show, parse
from symb import trees
def conv(t): return 0 if t == "S" else app(conv(t[0]), conv(t[1]))
SS = parse("SS"); BS = parse("S(SS)(SS)")
N = [BS]
for _ in range(14): N.append(app(SS, N[-1]))
idxN = {t: i for i, t in enumerate(N)}
found = []
for nb in range(1, 8):
    for B0t in trees(nb):
        B0 = conv(B0t)
        X = [B0]
        for _ in range(6): X.append(app(SS, X[-1]))
        idxX = {t: i for i, t in enumerate(X)}
        ok = True; rec = []
        for K in (1, 2, 3):
            for n in (1, 2):
                st = [0, X[0]] + [0] * n + [SS, SS, N[K], parse("SSS")]
                hit = None
                for step in range(1, 800):
                    if len(st) < 3: break
                    a, b, c = st[0], st[1], st[2]
                    st = spine(a) + [c, app(b, c)] + st[3:]
                    if st[0] == 0 and len(st) > 6 and st[1] in idxX and idxX[st[1]] >= 1:
                        m = 0
                        while st[2 + m] == 0 and 2 + m < len(st) - 3: m += 1
                        if m >= 1 and st[2 + m] == SS and st[3 + m] == SS and st[4 + m] in idxN:
                            hit = (step, idxX[st[1]], m, idxN[st[4 + m]]); break
                if hit is None: ok = False; break
                rec.append((K, n, hit))
            if not ok: break
        if ok: found.append((show(B0), rec))
print(len(found))
for f in found[:10]: print(f)
