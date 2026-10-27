"""Case (b) replay test.  Single-wrapper w = b0.c0 (pattern alpha: glue [c0, w, y] ++ R0), b0 != S.
Phase 3 = b0'.c0'.p'.y.(x.y).r.  Look for the first phase-3 list whose front is c0'.p' (no extra args);
then phase 3 continues from args(c0') ++ [p', t, ...] and phase 2 from args(c0) ++ [y, w.y, R0] (after the glue).
Map rho: p -> c, y -> p', (w.y) -> t.  Check that the top parts of the two runs stay rho-related until phase 2's
transfer, and that phase 3's front is then c-headed."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def rho(t, wy, tt, memo):
    if t in memo: return memo[t]
    if t == wy: r = tt
    elif t == Y: r = P          # y -> p'  (P is reused as p' in phase 3)
    elif t == P: r = C
    elif t <= 0: r = t
    else: r = hm.app(rho(hm.L[t], wy, tt, memo), rho(hm.R[t], wy, tt, memo))
    memo[t] = r
    return r
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark()
for D2 in data:
    lst = [Rr, Y, X, D2]; hist = []
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3]) and hm.R[lst[-3]] == Y):
        hm.truncate(M0); continue
    V = lst[-3]; w = hm.L[V]
    if hm.head(w) != 0 or hm.L[w] == 0: hm.truncate(M0); continue          # case (b) only
    b0, c0 = hm.L[w], hm.R[w]
    glue = max(t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y)
    if hist[glue][-1] != c0: st["not pattern alpha"] += 1; hm.truncate(M0); continue
    b0cl = P not in tg.atoms(b0)
    # phase-2 continuation after the glue: top part = list above (and including) w.y
    after = list(hist[glue + 1]) if glue + 1 < len(hist) else list(lst)
    wy = hm.app(w, Y)
    # phase 3
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    c0c = tg.subst(c0, P, C)
    s3 = [Rr, Y, X, D3]; found = None
    for t in range(1500):
        if len(s3) < 3 or hm.head(s3[-1]) != 0: break
        if s3[-1] == hm.app(c0c, P): found = t; break
        hm.step(s3)
    if found is None:
        h = hm.head(s3[-1]); st[("b0 closed" if b0cl else "b0 P", "no c0'.p' front", "reexec" if h == C else "other")] += 1
        hm.truncate(M0); continue
    tt = s3[-3]           # the element t (third) at the c0'.p' front
    hm.step(s3)           # open c0'.p'
    # now compare: phase-2 top part above w.y (inclusive) vs phase-3 top part
    p2 = after[:]         # stack, front last
    k2 = 0; ok = True; memo = {}
    while True:
        # compare tops: phase-2 elements down to w.y vs phase-3 same number of elements
        idx = p2.index(wy) if wy in p2 else None
        if idx is None: ok = False; break
        top2 = p2[idx:]
        top3 = s3[len(s3) - len(top2):]
        if [rho(e, wy, tt, memo) for e in top2] != top3: ok = False; break
        if len(p2) < 3 or hm.head(p2[-1]) != 0: break
        hm.step(p2); hm.step(s3); k2 += 1
        if k2 > 1500: break
    h2 = hm.head(p2[-1]); h3 = hm.head(s3[-1])
    st[("b0 closed" if b0cl else "b0 P", "replay ok" if ok else "replay breaks",
        "p2 front p" if h2 == P else "p2 other", "p3 front c" if h3 == C else ("p3 front p'" if h3 == P else "p3 other"))] += 1
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
