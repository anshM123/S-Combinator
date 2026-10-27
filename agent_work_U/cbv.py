"""Call-by-value (leftmost-innermost) for S-terms on VALUES (normal forms): S, S v, S v w.
apply(v, w): S*w = S w ; (S a)*w = S a w ; (S a b)*w = (a*w)*(b*w).  With a step budget (divergence -> None)."""
import sys
sys.setrecursionlimit(100000)
from dm import app, spine, show, size, parse, trees, mark, truncate, L, R

class Budget(Exception): pass
def mk_apply(budget):
    cnt = [0]
    memo = {}
    def ap(v, w):
        k = (v, w)
        if k in memo: return memo[k]
        cnt[0] += 1
        if cnt[0] > budget: raise Budget()
        args, h = spine(v)
        n = len(args)
        if n <= 1:
            r = app(v, w)
        else:
            a, b = args
            r = ap(ap(a, w), ap(b, w))
        memo[k] = r
        return r
    return ap, cnt
def nf_cbv(t, budget=100000):
    """normal form of an arbitrary term t (innermost), or None if budget exceeded"""
    ap, cnt = mk_apply(budget)
    def ev(t):
        if t <= 0: return t
        # evaluate function and argument to values, then apply
        f = ev(L[t]); x = ev(R[t])
        return ap(f, x)
    try:
        return ev(t)
    except Budget:
        return None
    except RecursionError:
        return None
if __name__ == "__main__":
    for s in ["SSS", "S(SS)S(SS)", "SSS(SS)", "S(SS)(SS)(SS)SS"]:
        t = parse(s); r = nf_cbv(t, 100000)
        print(s, "->", None if r is None else show(r))
