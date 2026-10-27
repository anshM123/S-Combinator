"""Phase-3-shaped single-level data D3 = W.p' (W random, contains frozen c, ordered: in every S-headed subterm the
c-free arguments come first; p' absent from W).  Look for proper transfers at POSITION 3 (p'-headed stuck front and
a proper right comb over y — y once, no x, r, != y — as the third element)."""
import sys, random, collections
import hm, transfer_graph as tg, chain3 as c3, phase2_general as pg
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def rand_term(n, pc):
    if n == 1: return C if random.random() < pc else 0
    k = random.randint(1, n - 1)
    return hm.app(rand_term(k, pc), rand_term(n - k, pc))
def proper(V):
    if V == Y: return False
    a = tg.atoms(V)
    if a.get(Y, 0) != 1 or a.get(X) or a.get(Rr): return False
    t = V
    while t != Y:
        if t <= 0: return False
        if Y in tg.atoms(hm.L[t]): return False
        t = hm.R[t]
    return True
if __name__ == "__main__":
    random.seed(int(sys.argv[1])); N = int(sys.argv[2]); W = int(sys.argv[3])
    M0 = hm.mark(); st = collections.Counter(); hits = []
    for it in range(N):
        Wt = rand_term(random.randint(2, W), 0.15)
        if C not in tg.atoms(Wt) or hm.head(Wt) != 0 or not pg.ordered(Wt): hm.truncate(M0); continue
        D3 = hm.app(Wt, P)
        lst = [Rr, Y, X, D3]
        s, k = hm.run(lst, 3000)
        if s == "stuck" and hm.head(lst[-1]) == P and len(lst) >= 3:
            if proper(lst[-3]):
                st["PROPER pos3"] += 1
                if len(hits) < 8: hits.append((hm.show(Wt), hm.show_list(lst, maxn=4)[:120]))
            else: st["p'-front, pos3 not proper"] += 1
        else:
            st[s if s != "stuck" else "stuck-" + ("c" if hm.head(lst[-1]) == C else "other")] += 1
        hm.truncate(M0)
    print(st)
    for h in hits: print(h)
