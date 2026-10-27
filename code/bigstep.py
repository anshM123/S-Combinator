"""Big-step head normalisation H/App with call-tree statistics, annotated by the finite model.

Terms: None = S, (l, r) = application.  hnf represented as tuple of components (0, 1 or 2 terms).
Records, for terminating runs, the longest chain of consecutive App tail calls and the classes seen.
"""
import sys
from functools import lru_cache
from verify_model import load

sys.setrecursionlimit(1000000)
reps, hn, TAB = load("../data/model35_hn.txt")
SCL = reps.index("S")

@lru_cache(None)
def cls(t):
    return SCL if t is None else int(TAB[cls(t[0]), cls(t[1])])

def app(a, b): return (a, b)

class Budget(Exception): pass

class Ev:
    def __init__(self, budget):
        self.steps = 0; self.budget = budget
        self.max_tail = 0; self.tail_examples = []
    def H(self, t):
        # left spine: t = S a1 ... ak
        args = []
        while t is not None:
            args.append(t[1]); t = t[0]
        args.reverse()
        if len(args) <= 2: return tuple(args)
        h = (args[0], args[1])
        for a in args[2:]:
            h = self.App(h, a)
        return h
    def App(self, h, v):
        tail = 0
        trace = []
        while True:
            if len(h) < 2: return h + (v,)
            p, q = h
            self.steps += 1
            if self.steps > self.budget: raise Budget()
            trace.append((cls(build(h)), cls(v)))
            hp = self.H(p)
            w = self.App(hp, v)
            h, v = w, (q, v)        # tail call App(w, q v)
            tail += 1
            if tail > self.max_tail:
                self.max_tail = tail; self.tail_examples = list(trace)

def build(h):
    t = None
    for c in h: t = (t, c)
    return t

def trees(n, memo={}):
    if n in memo: return memo[n]
    if n == 1: r = [None]
    else:
        r = []
        for i in range(1, n):
            for l in trees(i):
                for rr in trees(n - i):
                    r.append((l, rr))
    memo[n] = r
    return r

def show(t):
    if t is None: return "S"
    s = show(t[0]); r = t[1]
    return s + ("S" if r is None else "(" + show(r) + ")")

if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    for n in range(1, nmax + 1):
        best = 0; ex = None; extrace = None
        for t in trees(n):
            if not hn[cls(t)]: continue
            ev = Ev(10000)
            try:
                ev.H(t)
            except Budget:
                print("BUDGET FAIL (counterexample?)", show(t)); continue
            if ev.max_tail > best:
                best = ev.max_tail; ex = show(t); extrace = ev.tail_examples
        print(f"n={n}: longest App tail chain = {best} in {ex}; abstract (class(h),class(v)) along it: {extrace}")
        sys.stdout.flush()
