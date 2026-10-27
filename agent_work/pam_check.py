"""Hypotheses of Theorem PAM for real multi-wrapper handlers (innermost wrapper vn = b0.c0 glued in pattern alpha):
(1) the top part args(c0) ++ [y, vn.y] reaches a p-front with the guards; (2) at the first opening of an element
prefixed by the innermost level in phase 3, the element right below p' is y-free or the bare y.  Also: whether
phase 3 makes a proper transfer (it must not)."""
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
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3]) and hm.R[lst[-3]] != Y):
        hm.truncate(M0); continue
    V = lst[-3]
    ws = []; t = V
    while t != Y: ws.append(hm.L[t]); t = hm.R[t]
    vn = ws[-1]
    if hm.head(vn) != 0: st["innermost wrapper not S-headed (FH)"] += 1; hm.truncate(M0); continue
    b0, c0 = hm.L[vn], hm.R[vn]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == vn and L[-3] == Y]
    if not gl or hist[gl[-1]][-1] != c0: st["vn not pattern alpha"] += 1; hm.truncate(M0); continue
    if hm.head(b0) != 0 or hm.head(c0) != 0: st["b0/c0 not S-headed"] += 1; hm.truncate(M0); continue
    wy = hm.app(vn, Y); a0, _ = hm.spine(c0)
    T2 = [wy, Y] + list(reversed(a0)); guard = True
    while len(T2) >= 3 and hm.head(T2[-1]) == 0:
        if pre(T2[-1], wy) or hm.app(T2[-2], T2[-3]) == wy: guard = False
        hm.step(T2)
    h1 = guard and hm.head(T2[-1]) == P
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    Ln = hm.app(tg.subst(vn, P, C), P)
    s3 = [Rr, Y, X, D3]; b0ok = True; opened = False
    for t in range(3000):
        if len(s3) < 3 or hm.head(s3[-1]) != 0: break
        if not opened and pre(s3[-1], Ln):
            k0 = len(hm.spine(tg.subst(vn, P, C))[0])
            hm.step(s3); opened = True
            B0 = s3[-(k0 + 2)] if len(s3) >= k0 + 2 else None
            if B0 is not None and not (B0 == Y or Y not in tg.atoms(B0)): b0ok = False
            continue
        hm.step(s3)
    proper = len(s3) >= 3 and hm.head(s3[-1]) == P and T3.S3.proper(s3[-3])
    st[("hyp (1) " + ("ok" if h1 else "FAILS"), "hyp (2) " + ("ok" if b0ok else "FAILS"),
        "innermost opened" if opened else "never opened", "PROPER" if proper else "no proper transfer")] += 1
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
