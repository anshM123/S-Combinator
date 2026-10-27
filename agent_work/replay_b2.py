"""Case (b), b0 closed, phase 3 never has c0'.p' at the front: how does phase 3 end?"""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark(); ex = {}
for D2 in data:
    o2, V, _ = T3.phase(D2, 1500)
    if o2 != "proper3" or hm.R[V] != Y: hm.truncate(M0); continue
    w = hm.L[V]
    if hm.head(w) != 0 or hm.L[w] == 0: hm.truncate(M0); continue
    b0, c0 = hm.L[w], hm.R[w]
    if P in tg.atoms(b0): hm.truncate(M0); continue
    D3 = tg.subst(tg.subst(V, P, C), Y, P)
    c0c = tg.subst(c0, P, C)
    s3 = [Rr, Y, X, D3]; hit = False
    for t in range(1500):
        if len(s3) < 3 or hm.head(s3[-1]) != 0: break
        if s3[-1] == hm.app(c0c, P): hit = True; break
        hm.step(s3)
    if hit: hm.truncate(M0); continue
    h = hm.head(s3[-1])
    front = "c" if h == C else ("p'" if h == P else hm.NAMES.get(h, "?"))
    pos3 = s3[-3] if len(s3) >= 3 else None
    kind = "-" if pos3 is None else ("bare y" if pos3 == Y else ("P'" if (P in tg.atoms(pos3) and Y not in tg.atoms(pos3) and X not in tg.atoms(pos3)) else ("Y" if Y in tg.atoms(pos3) else "other")))
    st[("front " + front, "pos3 " + kind)] += 1
    ex.setdefault(("front " + front, "pos3 " + kind), (hm.show(D2), hm.show_list(s3, maxn=5)[:150].replace("p", "p'")))
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
for k, v in ex.items(): print("ex", k, v)
