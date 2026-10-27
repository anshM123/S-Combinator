"""Call-by-value at the root: the fixed-depth case of leftmost-innermost evolution (main agent, 2026-10-26).
LI contracts the head of S a1 a2 a3 … only after a1, a2, a3 are normal forms. At the root this is the head machine on a
list whose first three elements are normalised before every contraction:
  [a, b, c] ++ R  =>  spine(nf a) ++ [c, b·c] ++ R, then normalise the new first three.
If an element in the first three has no normal form, LI enters it and never returns (descent at the root). This runs the
root machine with a memoised normaliser and a step budget per normalisation (budget exceeded = treated as descent; a
heuristic), and reports terms whose root keeps contracting for N contractions, with the number of normalisations that
did real work (an element in the first three that was not already normal).
Usage: python cbv_root.py NMIN NMAX N BUDGET"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from li_explore import has_redex, terms, _red

class Budget(Exception):
    pass

_nf = {}
CAP = 2_500_000                                   # hard cap on hash-consed nodes (memory guard)
def nf(t, budget):
    """normal form of t by leftmost-outermost normalisation: the head machine on t's spine list (one new node per step)
    until a head normal form, then the arguments recursively; memoised; raises Budget after budget[0] head steps or when
    the node table exceeds CAP"""
    if not has_redex(t): return t
    r = _nf.get(t)
    if r is not None: return r
    args, h = hc.spine(t); stk = args[::-1]
    while len(stk) >= 3:
        budget[0] -= 1
        if budget[0] < 0 or len(hc.L) > CAP: raise Budget()
        a = stk.pop(); b = stk.pop(); c = stk.pop(); ch, hd = hc.spine(a)
        stk.append(hc.app(b, c)); stk.append(c); stk.extend(reversed(ch))
    u = 0
    for x in reversed(stk): u = hc.app(u, nf(x, budget))
    _nf[t] = u
    return u

def root_run(t, N, B):
    args, h = hc.spine(t)
    if len(args) < 3: return 0, 0, "hnf"
    stk = args[::-1]; work = 0
    for n in range(N):
        if len(stk) < 3: return n, work, "hnf"
        for i in (1, 2, 3):
            e = stk[-i]
            if has_redex(e):
                try:
                    stk[-i] = nf(e, [B]); work += 1
                except Budget:
                    return n, work, "descends (no normal form within budget)"
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
        if len(hc.L) > CAP: return n, work, "memory"
    return N, work, "root keeps contracting"

if __name__ == "__main__":
    NMIN, NMAX, N, B = (int(x) for x in sys.argv[1:5])
    tally = collections.Counter(); keep = []
    for n in range(NMIN, NMAX + 1):
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear(); _red.clear(); _nf.clear()
        srcs = [hc.show(t) for t in terms(n)]
        from symb import parse
        for src in srcs:
            if len(hc.L) > 2_000_000:
                hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear(); _red.clear(); _nf.clear()
            t = hc.from_tuple(parse(src))
            m, work, why = root_run(t, N, B)
            tally[(n, why)] += 1
            if why == "root keeps contracting": keep.append((n, src, work))
    for k, v in sorted(tally.items()): print(k, v)
    print("root keeps contracting (term, normalisations that did work):")
    for n, src, work in keep: print("  ", n, src, work)
