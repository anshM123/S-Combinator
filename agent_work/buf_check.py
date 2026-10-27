"""Candidate invariants in phase 3 (regions CL* C* P'* Y*):
  BUF : if the C-region is empty and the P'-region is nonempty, the P'-bottom is not p'-headed
  QP  : P'-region nonempty => contains a p'-headed element
  ORD : region order CL* C* P'* Y*
checked at every step of phase-3 runs from multi-level phase-2 outputs (right combs <= N leaves)."""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def cls(t):
    a = tg.atoms(t)
    if a.get(X) or a.get(Y) or a.get(Rr): return 3
    if a.get(P): return 2
    if a.get(C): return 1
    return 0
def check(L):
    cl = [cls(e) for e in L]
    if any(cl[i] > cl[i + 1] for i in range(len(cl) - 1)): return "ORD"
    Cn = cl.count(1); Pidx = [i for i in range(len(L)) if cl[i] == 2]
    if Pidx and not any(hm.head(L[i]) == P for i in Pidx): return "QP"
    if Cn == 0 and Pidx and hm.head(L[Pidx[-1]]) == P: return "BUF"
    return None
if __name__ == "__main__":
    N = int(sys.argv[1]); st = collections.Counter(); ex = {}
    data = [D for D in c3.rcombs(N) if hm.R[D] != P]
    M0 = hm.mark()
    for D in data:
        r, Vs = c3.phase(D, 4000)
        if r != "proper": hm.truncate(M0); continue
        for V in Vs:
            D3 = tg.subst(tg.subst(V, P, C), Y, P)
            lst = [Rr, Y, X, D3]
            viol = None
            for s in range(3000):
                v = check(list(reversed(lst)))
                if v and v not in ex: ex[v] = (hm.show(D3)[:50], s, hm.show_list(lst, maxn=6)[:140])
                if v: st[v] += 1
                if len(lst) < 3 or hm.step(lst) < 0: break
            st["runs"] += 1
        hm.truncate(M0)
    print(st)
    for k, v in ex.items(): print(k, v)
