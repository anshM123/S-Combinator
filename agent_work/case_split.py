"""Phase-3-shaped single-level data: classify runs by whether a sigma_C step happens (front in C, second = the only
P'-element, third in Y) and whether the run ends in a proper transfer at position 3."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg, p3shape_pos3 as S3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def cls(t):
    a = tg.atoms(t)
    if a.get(X) or a.get(Y) or a.get(Rr): return "Y"
    if a.get(P): return "P"
    if a.get(C): return "C"
    return "CL"
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2]); W = int(sys.argv[3])
    M0 = hm.mark(); st = collections.Counter()
    for it in range(N):
        Wt = S3.rand_term(random.randint(2, W), 0.15)
        if C not in tg.atoms(Wt) or hm.head(Wt) != 0 or not pg.ordered(Wt): hm.truncate(M0); continue
        lst = [Rr, Y, X, hm.app(Wt, P)]; sigma = False
        for s in range(3000):
            if len(lst) < 3: break
            a, b, c = lst[-1], lst[-2], lst[-3]
            if hm.head(a) != 0: break
            if cls(a) == "C" and cls(b) == "P" and cls(c) == "Y":
                if sum(1 for e in lst if cls(e) == "P") == 1: sigma = True
            hm.step(lst)
        prop = (len(lst) >= 3 and hm.head(lst[-1]) == P and S3.proper(lst[-3]))
        st[("sigma_C" if sigma else "no sigma"), ("PROPER" if prop else "-")] += 1
        hm.truncate(M0)
    print(st)
