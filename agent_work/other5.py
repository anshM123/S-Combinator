import sys
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
data = [D for D in c3.rcombs(int(sys.argv[1])) if hm.head(D) == 0]
M0 = hm.mark(); n = 0
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
    if a == c0 or (hm.L[c0] == 0 and hm.R[c0] == a): hm.truncate(M0); continue
    print("D2 =", hm.show(D2), " w =", hm.show(w), " glue front a =", hm.show(a))
    for L in hist[max(0, glue - 1): glue + 5]: print("   ", hm.show_list(list(L), maxn=6)[:160])
    D3 = tg.subst(tg.subst(lst[-3], P, C), Y, P)
    st = [Rr, Y, X, D3]
    for t in range(7):
        print("      3:", hm.show_list(st, maxn=6)[:160].replace("p", "p'"))
        if len(st) < 3 or hm.head(st[-1]) != 0: break
        hm.step(st)
    n += 1; hm.truncate(M0)
    if n >= 5: break
