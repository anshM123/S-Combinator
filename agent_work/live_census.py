"""(levels k of the datum, wrappers n of the proper position-3 handler, live?) where DEAD = some wrapper p-headed
(next datum has a frozen-headed level: FH) or outermost wrapper = bare S (next datum S.U: Lemma YD)."""
import sys, collections, random
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, ml_wrappers as MW
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
st = collections.Counter(); ex = {}
def wraps(V):
    ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    return ws
def go(D2):
    o2, V, _ = T3.phase(D2, 1500)
    if o2 == "proper3":
        k = len(MW.levels(D2)) - 1
        ws = wraps(V)
        dead = any(hm.head(w) == P for w in ws) or ws[0] == 0
        key = (k, len(ws), "dead" if dead else "LIVE")
        st[key] += 1
        ex.setdefault(key, (hm.show(D2), hm.show(V)))
mode = sys.argv[1]
if mode == "ex":
    data = [D for D in c3.rcombs(int(sys.argv[2])) if hm.head(D) == 0]
else:
    NK, WK, NT = map(int, sys.argv[2:5])
    Ks = [t for n in range(1, NK + 1) for t in hm.trees(n) if hm.head(t) == 0]
    wr = [t for n in range(1, WK + 1) for t in hm.trees(n)]
    tails = [P]; fr = [(P, 1)]
    while fr:
        nf = []
        for t, sz in fr:
            for d in wr:
                if sz + hm.size(d) <= NT:
                    u = hm.app(d, t); tails.append(u); nf.append((u, sz + hm.size(d)))
        fr = nf
    data = [hm.app(K, T) for T in tails if T != P for K in Ks]
M0 = hm.mark()
for D2 in data:
    go(D2); hm.truncate(M0)
for key in sorted(st): print(key, st[key])
for key in sorted(ex):
    if key[2] == "LIVE" and key[1] >= 2: print("ex", key, ex[key])
