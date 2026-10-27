"""Classify the forever-descending one-redex evolutions (main agent, 2026-10-26).
For every term up to NMAX leaves that keeps exactly one redex for N steps with at least N/2 descents, record the active
lists at descents after step N/4 and test them against the K-family mechanism: K = S(SS)(SS), Y_0 = K,
Y_{n+1} = S S Y_n, steady states [S, Y_j, Y_n] (j < n) and [SS, SS, Y_n]. Reports the terms that do not fit, with
the first non-fitting active list. Usage: python descent_classify.py NMAX N [NMIN]"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
import li_explore
from li_explore import has_redex, terms
from symb import parse

def run(t, N):
    L = list(hc.spine(t)[0]); lists = []
    for n in range(N):
        while len(L) < 3:
            red = [e for e in L if has_redex(e)]
            if len(red) != 1: return None
            L = list(hc.spine(red[0])[0]); lists.append((n, tuple(L)))
        if any(has_redex(e) for e in L): return None
        a, b, c = L[0], L[1], L[2]
        L = list(hc.spine(a)[0]) + [c, hc.app(b, c)] + L[3:]
    return lists

def family_index(y, SS, K):
    """n with y = Y_n, else None"""
    n = 0
    while y != K:
        args, _ = hc.spine(y)
        if len(args) != 2 or args[0] != 0 or y == 0: return None
        y = args[1]; n += 1
        if n > 100000: return None
    return n

if __name__ == "__main__":
    NMAX, N = int(sys.argv[1]), int(sys.argv[2])
    NMIN = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    SS = hc.from_tuple(parse("SS")); K = hc.from_tuple(parse("S(SS)(SS)"))
    for n in range(NMIN, NMAX + 1):
        fit = 0; misfit = []
        for t in terms(n):
            lists = run(t, N)
            if lists is None or len(lists) < N // 2: continue
            ok = True
            for step, L in lists:
                if step < N // 4: continue
                a, b, c = L
                nc = family_index(c, SS, K)
                if nc is None: ok = False
                elif a == SS and b == SS: pass
                elif a == 0:
                    nb = family_index(b, SS, K)
                    if nb is None or nb >= nc: ok = False
                else: ok = False
                if not ok:
                    misfit.append((hc.show(t), step, "[" + ", ".join(hc.show(e)[:40] for e in L) + "]")); break
            if ok: fit += 1
        print(f"{n} leaves: forever-descending (>= N/2 descents in {N} steps): {fit + len(misfit)}; "
              f"K-family steady state: {fit}; other: {len(misfit)}", flush=True)
        for m in misfit[:6]: print("   other:", m, flush=True)
