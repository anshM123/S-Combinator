"""At the x1-front of phase 3 (pattern alpha, single wrapper): the two elements e1, e2 that replace y and w.y in the
replay.  Phase 3's REEXEC replays phase 2's transfer with the handler w.y replaced by e2: what is e2?"""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
FROZ = set(c3.FROZ)
def pre(t, w):
    while True:
        if t == w: return True
        if t <= 0: return False
        t = hm.L[t]
def kind(e):
    if e == Y: return "y"
    if e == P: return "p'"
    a = tg.atoms(e); h = hm.head(e)
    hs = "p'-headed" if h == P else ("c-headed" if h in FROZ else ("y-headed" if h == Y else ("S-headed" if h == 0 else "other")))
    return hs + ("+y" if a.get(Y) else "") + ("+p'" if a.get(P) else "") + ("+c" if any(a.get(f) for f in FROZ) else "")
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark()
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
        f = s3[-1]
        if pre(f, c0c): ev = "x1"; break
        if hm.head(f) != 0: break
        hm.step(s3)
    if ev != "x1": hm.truncate(M0); continue
    hm.step(s3)
    n0 = len(hm.spine(c0)[0])
    e1, e2 = s3[-(n0 + 1)], s3[-(n0 + 2)]
    st[("e1: " + kind(e1), "e2: " + kind(e2))] += 1
    hm.truncate(M0)
for k in sorted(st, key=lambda k: -st[k]): print(k, st[k])
