"""Pattern-beta single-wrapper handlers: structure of (a1, w = b0.c0) where the glue step is [a1, w, y]."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark(); ex = {}
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
    if a1 == c0: hm.truncate(M0); continue
    c0args, _ = hm.spine(c0)
    rel = "c0 = S.a1" if (hm.L[c0] == 0 and hm.R[c0] == a1) else ("a1 in args(c0)" if a1 in c0args else ("a1 = c0-prefix?" if False else "other"))
    key = (rel, "b0=S" if b0 == 0 else ("b0 closed" if P not in tg.atoms(b0) else "b0 P"))
    st[key] += 1
    ex.setdefault(key, (hm.show(D2), "a1=" + hm.show(a1), "w=" + hm.show(w)))
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
for k, v in ex.items(): print("ex", k, v)
