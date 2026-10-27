"""Extended Church-chain model through a replayed re-execution.  In the replay class (single wrapper, pattern alpha,
x1-front reached in phase 3), phase 3's REEXEC replays phase 2's transfer with the handler w.y replaced by e2.  If the
frozen value then behaves as the live predecessor did after phase 2's transfer, the next datum is
D4 = e2[y := p'', p' := c'].  Run phase 4 from D4 and classify (and continue the chain by transfers)."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
C, C2, C3 = c3.FROZ[0], c3.FROZ[1], c3.FROZ[2]
def pre(t, w):
    while True:
        if t == w: return True
        if t <= 0: return False
        t = hm.L[t]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark(); ex = {}
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3" or hm.R[V] != Y: hm.truncate(M0); continue
    w = hm.L[V]
    if hm.head(w) != 0: hm.truncate(M0); continue
    b0, c0 = hm.L[w], hm.R[w]
    D3 = tg.subst(tg.subst(V, P, C), Y, P); c0c = tg.subst(c0, P, C)
    s3 = [Rr, Y, X, D3]; hm.step(s3); ev = None
    for t in range(3000):
        if len(s3) < 3: break
        if pre(s3[-1], c0c): ev = "x1"; break
        if hm.head(s3[-1]) != 0: break
        hm.step(s3)
    if ev != "x1": hm.truncate(M0); continue
    hm.step(s3)
    n0 = len(hm.spine(c0)[0])
    e2 = s3[-(n0 + 2)]
    # next datum in the extended model: e2[y := p'', p' := c']  (p'' reuses atom P after renaming p' -> C2)
    D4 = tg.subst(tg.subst(e2, P, C2), Y, P)
    a = tg.atoms(D4)
    if not a.get(P): kind = "D4 has no live predecessor (no transfer possible)"
    elif hm.head(D4) == P: kind = "D4 = p''-headed (identity / immediate front)"
    elif hm.head(D4) != 0: kind = "D4 frozen-headed (FH: immediate re-execution)"
    else:
        ln = 0; D = D4
        for ph in range(4):
            o, VV, _ = T3.phase(D, 2000)
            if o != "proper3": break
            ln += 1; D = tg.subst(tg.subst(VV, P, c3.FROZ[3 + ph]), Y, P)
        kind = "D4 genuine datum: %d further proper transfers" % ln
    st[kind] += 1
    ex.setdefault(kind, (hm.show(D2), hm.show(e2)))
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
for k, v in ex.items(): print("ex", k, v)
