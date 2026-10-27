"""Unified pattern-alpha test.  Real single-wrapper handlers V = w.y with w = b0.c0 glued by [c0, w, y] ++ R0.
Phase 3 (datum w[p:=c].p') runs as the generic run of b0' on (c0', p', y, x.y, r) until the first front that is
c0'-prefixed (x1), p'-headed (x2) or frozen-headed.  Barrier lemma: y, x.y, r untouched until then.
x1-front c0'.u: opening it gives args(c0') ++ [e1, e2, ...]; rho = (y -> e1, w.y -> e2, p -> c) should map the
phase-2 top part after the glue (args c0 ++ [y, w.y]) step by step onto phase 3's top part, ending in a c-front at
phase 2's transfer.  Guards on phase 2: no (w.y)-prefixed front, no step creating w.y."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
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
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark(); bad = []
for D2 in data:
    lst = [Rr, Y, X, D2]; hist = []
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3]) and hm.R[lst[-3]] == Y):
        hm.truncate(M0); continue
    V = lst[-3]; w = hm.L[V]
    if hm.head(w) == P: st["PH (FH)"] += 1; hm.truncate(M0); continue
    b0, c0 = hm.L[w], hm.R[w]
    glue = max(t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y)
    if hist[glue][-1] != c0: st["pattern beta"] += 1; hm.truncate(M0); continue
    wy = hm.app(w, Y)
    # phase-2 top part right after the glue: args(c0) ++ [y, w.y]   (stack: front last)
    a0, _ = hm.spine(c0)
    T2 = [wy, Y] + list(reversed(a0))
    guard = True; T2run = T2[:]
    while len(T2run) >= 3 and hm.head(T2run[-1]) == 0:
        if pre(T2run[-1], wy) or hm.app(T2run[-2], T2run[-3]) == wy: guard = False
        hm.step(T2run)
    p2front = len(T2run) >= 1 and hm.head(T2run[-1]) == P
    # phase 3
    D3 = tg.subst(tg.subst(V, P, C), Y, P); c0c = tg.subst(c0, P, C)
    s3 = [Rr, Y, X, D3]; hm.step(s3)
    ev = None
    for t in range(3000):
        if len(s3) < 3: ev = "hnf"; break
        f = s3[-1]
        if pre(f, c0c): ev = "x1"; break
        h = hm.head(f)
        if h == P: ev = "x2"; break
        if h in FROZ: ev = "frozen"; break
        if h != 0: ev = "other-atom"; break
        hm.step(s3)
    if ev is None: ev = "budget"
    if ev == "x2":
        proper = T3.S3.proper(s3[-3]) if len(s3) >= 3 else False
        st[("x2-front", "PROPER?!" if proper else "non-proper")] += 1
    elif ev == "x1":
        hm.step(s3)                     # open the x1 element
        n0 = len(a0)
        e1, e2 = s3[-(n0 + 1)], s3[-(n0 + 2)]
        memo = {}; ok = True
        P2 = T2[:]; S3l = s3[:]
        while True:
            top3 = S3l[len(S3l) - len(P2):] if len(S3l) >= len(P2) else None
            img = [rho(e, wy, e1, e2, memo) for e in P2]
            if top3 is None or img != top3: ok = False; break
            if len(P2) < 3 or hm.head(P2[-1]) != 0: break
            hm.step(P2); hm.step(S3l)
        endc = hm.head(S3l[-1]) == C
        st[("x1-front", "guards ok" if guard else "GUARD FAIL", "phase2 top -> p-front" if p2front else "phase2 top other",
            "replay ok" if ok else "REPLAY BREAKS", "phase3 c-front" if endc else "phase3 other")] += 1
        if not (ok and endc and guard and p2front) and len(bad) < 5: bad.append(hm.show(D2))
    else:
        st[(ev,)] += 1
    hm.truncate(M0)
for k in sorted(st, key=str): print(k, st[k])
for b in bad: print("check:", b)
