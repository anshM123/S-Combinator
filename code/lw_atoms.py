"""Leftmost-path finite half, new angle (main agent, 2026-10-27): for every term t <= NMAX leaves in the resisting joint
classes {(14,28), (14,26)} of L36 x M35, run the head machine on args(t) ++ [a, b] with opaque atoms a, b.
Generalised Lemma P (any two bottom elements): if this run stops (atom-headed front, or <= 2 elements), the leftmost
Böhm-tree path of t is finite. Reports how each run ends: 'a' / 'b' (stuck at an atom-headed front), 'hnf' (<= 2
elements; impossible for M35 class 28 or 26), 'cap' (no stop within CAP steps).
Usage: python lw_atoms.py NMAX [CAP]"""
import sys, collections
sys.setrecursionlimit(100000)
import hc
from li_explore import terms
from lw_anatomy import cls

def tup(i):
    if i == 0: return "S"
    return (tup(hc.L[i]), tup(hc.R[i]))

def spine(t):
    a = []
    while isinstance(t, tuple):
        a.append(t[1]); t = t[0]
    a.reverse()
    return t, a

def size(t):
    return 1 if not isinstance(t, tuple) else size(t[0]) + size(t[1])

def run_atoms(t, cap):
    L = spine(t)[1] + ["a", "b"]
    for k in range(cap):
        if len(L) <= 2: return "hnf", k
        h, ar = spine(L[0])
        if h != "S": return h, k
        L = ar + [L[2], (L[1], L[2])] + L[3:]
        if sum(size(x) for x in L) > 200000: return "big", k
    return "cap", cap

if __name__ == "__main__":
    NMAX = int(sys.argv[1]); CAP = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    target = {(14, 28), (14, 26)}
    for n in range(3, NMAX + 1):
        ends = collections.Counter(); ex = {}
        for t in terms(n):
            c = cls(t)
            if c not in target: continue
            e, k = run_atoms(tup(t), CAP)
            ends[(c, e)] += 1
            ex.setdefault((c, e), (hc.show(t), k))
        if ends:
            print(f"{n} leaves: " + ", ".join(f"{c}->{e}: {m}" for (c, e), m in sorted(ends.items())))
            for key, (s, k) in sorted(ex.items()):
                print(f"     e.g. {key}: {s}  ({k} steps)")
