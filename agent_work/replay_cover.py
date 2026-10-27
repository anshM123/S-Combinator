"""Which real single-wrapper transfers with w = S.c0 are covered by replay_glue (glue top [c0, w, y]) or by
replay_beta (w = S.(S.a1), glue top [a1, w, y]); check that the top-part run reaches a p-front with the guards."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, target3 as T3, prefix_replay as PR
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
st = collections.Counter(); M0 = hm.mark()
for D2 in data:
    lst = [Rr, Y, X, D2]; hist = []
    for t in range(1500):
        if len(lst) < 3 or hm.head(lst[-1]) != 0: break
        hist.append(tuple(lst)); hm.step(lst)
    if not (len(lst) >= 3 and hm.head(lst[-1]) == P and T3.S3.proper(lst[-3]) and hm.R[lst[-3]] == Y):
        hm.truncate(M0); continue
    w = hm.L[lst[-3]]
    if hm.head(w) != 0 or hm.L[w] != 0: hm.truncate(M0); continue
    c0 = hm.R[w]
    glue = max(t for t, L in enumerate(hist) if len(L) >= 3 and L[-2] == w and L[-3] == Y)
    a = hist[glue][-1]
    if a == c0: kind = "alpha (replay_glue)"
    elif hm.L[c0] == 0 and hm.R[c0] == a: kind = "beta w=S(S a1) (replay_beta)"
    else: kind = "other"
    T = [Y, w, a]; guard = True
    for t in range(1500):
        if len(T) < 3 or hm.head(T[-1]) != 0: break
        if PR.wpre(T[-1], w) or hm.app(T[-2], T[-3]) == w: guard = False
        hm.step(T)
    ok = len(T) >= 3 and hm.head(T[-1]) == P
    st[(kind, "top run -> p-front" if ok else "top run ends otherwise", "guards ok" if guard else "GUARD FAIL")] += 1
    hm.truncate(M0)
for k in sorted(st): print(k, st[k])
