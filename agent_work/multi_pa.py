"""Multi-wrapper live handlers: PA at the innermost level.  In phase 3 find the first opening of an element prefixed
by the innermost level L'_n = vn'.p' (exposes p').  Record B0 = the element right below the released p'.  Then the
PA barrier phase (vn = b0.c0) runs until the first c0'-prefixed / p'-headed / frozen front; at a c0'-prefixed front
check the replay of phase 2's continuation from vn's glue step (args(c0) ++ [y, vn.y]) under rho."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, fhl_cover as FC
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
FROZ = set(c3.FROZ)
def pre(t, w):
    while True:
        if t == w: return True
        if t <= 0: return False
        t = hm.L[t]
def rho(t, wy, e1, e2, memo):
    if t in memo: return memo[t]
    if t == wy: r = e2
    elif t == Y: r = e1
    elif t == P: r = C
    elif t <= 0: r = t
    else: r = hm.app(rho(hm.L[t], wy, e1, e2, memo), rho(hm.R[t], wy, e1, e2, memo))
    memo[t] = r
    return r
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
    if any(FC.lp_reaches_p(w) for w in ws) or ws[0] == 0: hm.truncate(M0); continue
    vn = ws[-1]; b0, c0 = hm.L[vn], hm.R[vn]
    gl = [t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == vn and L[-3] == Y]
    if not gl: st["vn glue not found"] += 1; hm.truncate(M0); continue
    g = gl[-1]
    if hist[g][-1] != c0: st["vn glued in pattern beta"] += 1; hm.truncate(M0); continue
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    Ln = hm.app(tg.subst(vn, P, C), P)
    s3 = [Rr, Y, X, D3]; opened = False
    for t in range(3000):
        if len(s3) < 3 or hm.head(s3[-1]) != 0: break
        if pre(s3[-1], Ln):
            hm.step(s3); opened = True; break
        hm.step(s3)
    if not opened:
        h = hm.head(s3[-1]); st[("innermost never opened", "reexec" if h == C else "other")] += 1; hm.truncate(M0); continue
    # after opening: args(vn') ++ [p', B0, ...]
    a_vn, _ = hm.spine(tg.subst(vn, P, C))
    k0 = len(a_vn)
    B0 = s3[-(k0 + 2)] if len(s3) >= k0 + 2 else None
    b0kind = "B0=y" if B0 == Y else ("B0 y-free" if B0 is not None and Y not in tg.atoms(B0) else ("B0 PROPER" if B0 is not None and T3.S3.proper(B0) else "B0 other"))
    # PA barrier phase
    c0c = tg.subst(c0, P, C)
    ev = None
    for t in range(3000):
        if len(s3) < 3: ev = "hnf"; break
        f = s3[-1]
        if pre(f, c0c): ev = "x1"; break
        h = hm.head(f)
        if h == P: ev = "x2"; break
        if h in FROZ: ev = "frozen"; break
        if h != 0: ev = "atom"; break
        hm.step(s3)
    if ev == "x2":
        st[(b0kind, "x2", "PROPER?!" if T3.S3.proper(s3[-3]) else "non-proper")] += 1
    elif ev == "x1":
        hm.step(s3)
        n0 = len(hm.spine(c0)[0])
        e1, e2 = s3[-(n0 + 1)], s3[-(n0 + 2)]
        wy = hm.app(vn, Y)
        a0, _ = hm.spine(c0)
        P2 = [wy, Y] + list(reversed(a0)); S3l = s3[:]; memo = {}; ok = True; guard = True
        while True:
            top = S3l[len(S3l) - len(P2):] if len(S3l) >= len(P2) else None
            if top is None or [rho(e, wy, e1, e2, memo) for e in P2] != top: ok = False; break
            if len(P2) < 3 or hm.head(P2[-1]) != 0: break
            if pre(P2[-1], wy) or hm.app(P2[-2], P2[-3]) == wy: guard = False
            hm.step(P2); hm.step(S3l)
        st[(b0kind, "x1", "guards ok" if guard else "GUARD FAIL", "replay ok" if ok else "REPLAY BREAKS",
            "p2 p-front" if hm.head(P2[-1]) == P else "p2 other", "p3 c-front" if hm.head(S3l[-1]) == C else "p3 other")] += 1
    else:
        st[(b0kind, ev)] += 1
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
