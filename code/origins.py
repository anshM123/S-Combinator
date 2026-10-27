"""Origin-tracking head reduction for S-terms (analysis of 'fast-or-never' head normalization).

An element is a node object with a unique origin id and a list of child elements.
Original term nodes get origins 0..; each created compound b.c gets a fresh origin.
Opening an element pushes its children (same objects => same origins), then c, then a new
compound node whose children are b.children + [c].  We count openings per origin.
"""
import sys, itertools
from functools import lru_cache

sys.setrecursionlimit(100000)

class N:
    __slots__ = ("o", "ch")
    def __init__(self, o, ch):
        self.o = o; self.ch = ch

def catalan_trees(n):
    # all binary trees with n leaves as nested tuples; leaf = None
    @lru_cache(None)
    def gen(k):
        if k == 1:
            return (None,)
        out = []
        for i in range(1, k):
            for l in gen(i):
                for r in gen(k - i):
                    out.append((l, r))
        return tuple(out)
    return gen(n)

def to_rose(t, ctr):
    """binary tree -> rose element (S x1..xk), assigning fresh origins to every rose node"""
    args = []
    while t is not None:
        args.append(t[1]); t = t[0]
    args.reverse()
    node = N(next(ctr), None)
    node.ch = [to_rose(a, ctr) for a in args]
    return node

def show_bin(t):
    if t is None: return "S"
    l, r = t
    s = show_bin(l)
    return s + ("S" if r is None else "(" + show_bin(r) + ")")

def run(t, maxsteps):
    ctr = itertools.count()
    root = to_rose(t, ctr)
    norig = next(ctr)
    stack = list(reversed(root.ch))  # top at end
    opens = {}
    steps = 0
    first3 = None
    created_opened = 0
    while len(stack) >= 3:
        if steps >= maxsteps:
            return ("div", steps, opens, norig, first3, created_opened)
        a = stack.pop(); b = stack.pop(); c = stack.pop()
        opens[a.o] = opens.get(a.o, 0) + 1
        if a.o >= norig: created_opened += 1
        if opens[a.o] >= 3 and first3 is None: first3 = steps
        bc = N(next(ctr), b.ch + [c])
        stack.append(bc); stack.append(c)
        stack.extend(reversed(a.ch))
        steps += 1
    return ("hnf", steps, opens, norig, first3, created_opened)

if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    budget = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    for n in range(1, nmax + 1):
        mx_open_term = 0; ex_term = None
        hnf3 = 0        # terminating runs in which some origin opened >= 3 times
        div_no3 = 0     # non-terminating (within budget) runs where no origin reached 3 openings
        maxfirst3 = -1; ex_first3 = None
        maxcreated = 0; ex_created = None
        cnt = [0, 0]
        for t in catalan_trees(n):
            kind, steps, opens, norig, first3, created = run(t, budget)
            m = max(opens.values()) if opens else 0
            if kind == "hnf":
                cnt[0] += 1
                if m > mx_open_term: mx_open_term, ex_term = m, show_bin(t)
                if m >= 3: hnf3 += 1
                if created > maxcreated: maxcreated, ex_created = created, show_bin(t)
            else:
                cnt[1] += 1
                if first3 is None: div_no3 += 1
                elif first3 > maxfirst3: maxfirst3, ex_first3 = first3, show_bin(t)
        print(f"n={n} hnf={cnt[0]} div={cnt[1]} | terminating: max opens/origin={mx_open_term} ({ex_term}), "
              f"runs with an origin opened>=3: {hnf3}, max created-openings={maxcreated} ({ex_created}) | "
              f"diverging: no origin reached 3 opens: {div_no3}, latest first-3rd-open step={maxfirst3} ({ex_first3})")
        sys.stdout.flush()
