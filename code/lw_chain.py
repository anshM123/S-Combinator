"""Computed leftmost steps inside the resisting component {(14,28),(14,26)} (main agent, 2026-10-27): for u = S e1..em
(m >= 3) the child is a right comb q_{k-1}.(...(q_0.e_m)) over the last argument (Theorem Q10's tail chain). Prints the
distribution of k and the chain values q_i for transitions that stay inside the component. Usage: python lw_chain.py NMAX"""
import sys, collections
sys.setrecursionlimit(100000)
import hc
from li_explore import terms
from lw_anatomy import cls, hnf

TGT = {(14, 28), (14, 26)}

def comb_over(x, e):
    """write x = q_{k-1}.(...(q_0.e)); return [q_{k-1}, ..., q_0] or None if e is not the bottom"""
    qs = []
    while x != e:
        if x == 0: return None
        qs.append(hc.L[x]); x = hc.R[x]
    return qs

if __name__ == "__main__":
    NMAX = int(sys.argv[1])
    ks = collections.Counter(); shapes = collections.Counter(); ex = {}
    seen = set()
    todo = []
    for n in range(3, NMAX + 1):
        for t in terms(n):
            if cls(t) in TGT: todo.append(t)
    while todo:
        u = todo.pop()
        if u in seen: continue
        seen.add(u)
        args = hc.spine(u)[0]
        if len(args) <= 2:
            x = args[0]
            if cls(x) in TGT: todo.append(x)
            continue
        L = hnf(u)
        if L is None or len(L) == 0: continue
        x = L[0]
        if cls(x) not in TGT: continue
        qs = comb_over(x, args[-1])
        k = None if qs is None else len(qs)
        ks[(cls(u), cls(x), k)] += 1
        if qs is not None:
            key = tuple(hc.show(q) for q in qs)
            shapes[key] += 1
            ex.setdefault(key, (hc.show(u), hc.show(x)))
        if hc.size(x) < 400: todo.append(x)
    print("transitions (class u, class child, k):", dict(ks))
    print("distinct chains:", len(shapes))
    for key, m in shapes.most_common(25):
        u, x = ex[key]
        print(f"  {m:5d}  q = {list(key)}   e.g. {u[:60]} -> {x[:60]}")
