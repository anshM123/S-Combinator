"""Replay with psi = [w -> y, y -> p'.y, p -> c] (w = innermost wrapper of the single-wrapper phase-2 handler).
Alignment = some phase-3 list equals psi(some phase-2 list) on the top K elements (K = all, or the elements above
the original x.y)."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, replay2 as R2
P, Y, X, Rr, C, PP = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0], R2.PP
def psi(t, w, memo):
    if t in memo: return memo[t]
    if t == w: r = Y
    elif t == Y: r = hm.app(PP, Y)
    elif t == P: r = C
    elif t <= 0: r = t
    else: r = hm.app(psi(hm.L[t], w, memo), psi(hm.R[t], w, memo))
    memo[t] = r
    return r
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark(); XY = hm.app(X, Y)
for D2 in data:
    L2 = R2.run_lists([Rr, Y, X, D2], 1500)
    last = list(L2[-1])
    if not (len(last) >= 3 and hm.head(last[-1]) == P and T3.S3.proper(last[-3])): hm.truncate(M0); continue
    V = last[-3]
    if hm.R[V] != Y: hm.truncate(M0); continue
    w = hm.L[V]
    if hm.head(w) != 0: hm.truncate(M0); continue
    D3 = hm.app(tg.subst(w, P, C), PP)
    L3 = R2.run_lists([Rr, Y, X, D3], 1500)
    memo = {}
    def top(L):  # elements above the original x.y / r tail (list stored front-last)
        L = list(L)
        while L and L[0] in (Rr,): L = L[1:]
        return tuple(L)
    img = {}
    for t, L in enumerate(L2):
        img.setdefault(tuple(psi(e, w, memo) for e in L), t)
    found = None
    for s, M in enumerate(L3):
        if M in img: found = (s, img[M]); break
    end3 = L3[-1]; h3 = hm.head(end3[-1]) if end3 else None
    o3 = "reexec" if h3 == C else ("p'-front" if h3 == PP else "other")
    st[("psi-aligned" if found else "not psi-aligned", o3)] += 1
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
