"""Prefix replay for single-wrapper handlers w = S.c0 (b0 = S).  T0 = [c0, w, y] (top part at the glue step).
Run phase 2 from T0 alone (front first) until a stuck front; check the replay guards (no w-prefixed front, no step
creating w); run phase 3 from [c0[c], p', y, x.y, r] and compare with theta(T_k) on the top part."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, replay2 as R2
P, Y, X, Rr, C, PP = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0], R2.PP
def wpre(t, w):
    while True:
        if t == w: return True
        if t <= 0: return False
        t = hm.L[t]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark()
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3" or hm.R[V] != Y: hm.truncate(M0); continue
    w = hm.L[V]
    if hm.head(w) != 0 or hm.L[w] != 0: hm.truncate(M0); continue      # need w = S.c0
    c0 = hm.R[w]
    T = [Y, w, c0]                    # stack: front last
    guard = True; steps = 0
    for t in range(1500):
        if len(T) < 3: break
        a, b, c = T[-1], T[-2], T[-3]
        if hm.head(a) != 0: break
        if wpre(a, w) or hm.app(b, c) == w: guard = False
        hm.step(T); steps += 1
    front_p = len(T) >= 3 and hm.head(T[-1]) == P
    memo = {}
    img = [R2.theta(e, w, memo) for e in T]
    c0c = tg.subst(c0, P, C)
    M = [Rr, hm.app(X, Y), Y, PP, c0c]
    s3 = 0
    for t in range(steps):
        if len(M) < 3 or hm.head(M[-1]) != 0: break
        hm.step(M); s3 += 1
    agree = M[-len(img):] == img if len(M) >= len(img) else False
    st[("phase2 from T0 ends p-front" if front_p else "T0 run ends otherwise", "guards ok" if guard else "GUARD FAILS",
        "phase3 top = theta(T_k)" if agree else "no agreement", "phase3 front c" if hm.head(M[-1]) == C else "phase3 front other")] += 1
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
