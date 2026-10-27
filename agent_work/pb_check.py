"""Check the hypotheses of Theorem PB on real pattern-beta single-wrapper handlers: w = b0.(S.a1), glue [a1, w, y];
the top part args(a1) ++ [y, w.y] must reach a p-front with the guards (no (w.y)-prefixed front, w.y not re-created);
b0 and a1 S-headed."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def pre(t, w):
    while True:
        if t == w: return True
        if t <= 0: return False
        t = hm.L[t]
if sys.argv[1] == "t":
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
else:
    data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark()
for D2 in data:
    lst = [Rr, Y, X, D2]; hist = []
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3]) and hm.R[lst[-3]] == Y):
        hm.truncate(M0); continue
    w = hm.L[lst[-3]]
    if hm.head(w) == P: hm.truncate(M0); continue
    b0, c0 = hm.L[w], hm.R[w]
    glue = max(t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y)
    a1 = hist[glue][-1]
    if a1 == c0: hm.truncate(M0); continue            # pattern alpha
    if not (hm.L[c0] == 0 and hm.R[c0] == a1): st["beta, c0 != S.a1"] += 1; hm.truncate(M0); continue
    wy = hm.app(w, Y)
    a0, _ = hm.spine(a1)
    T2 = [wy, Y] + list(reversed(a0)); guard = True
    while len(T2) >= 3 and hm.head(T2[-1]) == 0:
        if pre(T2[-1], wy) or hm.app(T2[-2], T2[-3]) == wy: guard = False
        hm.step(T2)
    ok = len(T2) >= 1 and hm.head(T2[-1]) == P
    D3 = tg.subst(tg.subst(lst[-3], P, C), Y, P)
    s3 = [Rr, Y, X, D3]; s, k = hm.run(s3, 3000)
    proper = s == "stuck" and hm.head(s3[-1]) == P and len(s3) >= 3 and T3.S3.proper(s3[-3])
    st[("beta, c0 = S.a1", "b0 S-headed" if hm.head(b0) == 0 else "b0 atom", "a1 S-headed" if hm.head(a1) == 0 else "a1 atom",
        "guards ok" if guard else "GUARD FAIL", "top -> p-front" if ok else "top other", "phase3 PROPER" if proper else "phase3 not proper")] += 1
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
