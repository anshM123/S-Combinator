"""Multi-level SL (MSL) candidate invariants in PHASE 2, multi-level right-comb data D = d1.(d2.(...(dk.p))).
LP*(e): stripping right arguments from e reaches some level L_j, j >= 2 (L_{k+1} = p, so p-headed counts).
  MQ : P-region nonempty => contains an LP* element
  MT : |P| = 2 => every non-LP* element of P has all its P spine args LP*
  MA : every LP* list element L_j.w1...wn (n >= 1): each P-element among the w's is LP* or has all P-args LP*
  GL : a step gluing a P-element b onto a Y-element: b is LP* or has all P-args LP*"""
import sys, collections
import hm, transfer_graph as tg, chain3 as c3, ml_wrappers as MW
P, Y, X, Rr = c3.P, c3.Y, c3.X, c3.Rr
def cls(t):
    a = tg.atoms(t)
    if a.get(X) or a.get(Y) or a.get(Rr): return 2
    if a.get(P): return 1
    return 0
def prefix_args(e, Ls):
    """if e = L_j . w1 ... wn return (j, [w1..wn]) else None"""
    ws = []; t = e
    while True:
        if t in Ls[1:]: return (Ls.index(t), list(reversed(ws)))
        if t <= 0: return None
        ws.append(hm.R[t]); t = hm.L[t]
def lp(e, Ls): return prefix_args(e, Ls) is not None
def pargs_lp(e, Ls):
    args, _ = hm.spine(e)
    return all(lp(a, Ls) for a in args if cls(a) == 1)
def check(L, Ls):
    # only the part above the Y-region matters for MQ/MT/MA; keep the first Y element for GL
    cut = 0
    while cut < len(L) and cls(L[cut]) != 2: cut += 1
    full = L
    L = L[:cut + 1]
    cl = [cls(e) for e in L]
    Pel = [e for e, c in zip(L, cl) if c == 1]
    if Pel and not any(lp(e, Ls) for e in Pel): return "MQ"
    if len(Pel) == 2:
        for e in Pel:
            if not lp(e, Ls) and not pargs_lp(e, Ls): return "MT"
    for e in full:
        c = cls(e)
        if c in (1, 2):
            pa = prefix_args(e, Ls)
            if pa and pa[1]:
                Pw = [w for w in pa[1] if cls(w) == 1]
                if len(Pw) == 1 and not lp(Pw[0], Ls) and not pargs_lp(Pw[0], Ls): return "MA1"
    if len(L) >= 3 and hm.head(L[0]) == 0 and cl[1] == 1 and cl[2] == 2:
        if not lp(L[1], Ls) and not pargs_lp(L[1], Ls): return "GL"
    return None
if __name__ == "__main__":
    N = int(sys.argv[1]); st = collections.Counter(); ex = {}
    data = [D for D in c3.rcombs(N) if hm.R[D] != P]
    M0 = hm.mark()
    for D in data:
        Ls = MW.levels(D)
        lst = [Rr, Y, X, D]
        for s in range(500):
            v = check(list(reversed(lst)), Ls) if s > 0 else None
            if v:
                st[v] += 1
                ex.setdefault(v, (hm.show(D), s, hm.show_list(lst, maxn=5)[:140]))
                break
            if len(lst) < 3 or hm.step(lst) < 0: break
        st["runs"] += 1
        hm.truncate(M0)
    print(st)
    for k, v in ex.items(): print(k, v)
