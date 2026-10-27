"""Multi-wrapper phase-2 handlers V = v1.(v2.(...(vn.y))), n >= 2: classify the outer wrappers v1..v_{n-1}
(closed: 'S' if bare S, 'CL-S..' S-headed closed; P: 'PH' p-headed, 'P-S' S-headed P) and the phase-3 outcome."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def cl(t):
    a = tg.atoms(t)
    if t == 0: return "S"
    if a.get(P): return "PH" if hm.head(t) == P else "P-S"
    return "CL"
mode = sys.argv[1]
if mode == "ex": data = [D for D in c3.rcombs(int(sys.argv[2])) if hm.head(D) == 0]
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
st = collections.Counter(); ex = {}; M0 = hm.mark()
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 == "proper3" and hm.R[V] != Y:
        ws = []; t = V
        while t != Y: ws.append(hm.L[t]); t = hm.R[t]
        key = tuple(cl(v) for v in ws[:-1])
        D3 = tg.subst(tg.subst(V, P, C), Y, P)
        o3, _, _ = T3.phase(D3, 1500)
        st[(key, o3)] += 1
        ex.setdefault(key, (hm.show(D2), hm.show(V)))
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
for k, v in ex.items(): print("ex", k, v)
