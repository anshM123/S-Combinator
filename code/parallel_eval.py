"""Wolfram's standard (ReplaceAll) evaluation on hash-consed S-terms (main agent): one pass replaces every outermost
non-overlapping redex S x y z -> x z (y z) (no reduction inside the instantiated x, y, z in the same pass), scanning
top-down. Memoised per DAG node, so sizes far beyond memory are fine. Prints the size sequence and its ratios."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
def step_fn():
    memo = {}
    def step(t):
        if t <= 0: return t
        r = memo.get(t)
        if r is not None: return r
        f, z = hc.L[t], hc.R[t]
        if f > 0 and hc.L[f] > 0 and hc.L[hc.L[f]] == 0:      # t = S x y z
            x, y = hc.R[hc.L[f]], hc.R[f]
            r = hc.app(hc.app(x, z), hc.app(y, z))
        else:
            r = hc.app(step(f), step(z))
        memo[t] = r; return r
    return step
size_memo = {}
def size(t):
    if t <= 0: return 1
    s = size_memo.get(t)
    if s is None: s = size(hc.L[t]) + size(hc.R[t]); size_memo[t] = s
    return s
if __name__ == "__main__":
    src, N = sys.argv[1], int(sys.argv[2])
    t = hc.from_tuple(parse(src)); sizes = [size(t)]; fixed = None
    for n in range(N):
        u = step_fn()(t)
        if u == t: fixed = n; break
        t = u; sizes.append(size(t))
    print(src, "normal form after", fixed, "steps" if fixed is not None else f"(no fixpoint in {N} steps)")
    print("  sizes:", sizes[:40] if len(sizes) <= 40 else sizes[:25] + ["..."] + sizes[-3:])
    r = [round(b / a, 3) for a, b in zip(sizes, sizes[1:])]
    print("  ratios (last 24):", r[-24:])
    d = [b - a for a, b in zip(sizes, sizes[1:])]
    print("  differences (first 30):", d[:30])
