"""Symbolic head machine for S-terms with opaque variables.

Terms: 'S' (the combinator), any other str = opaque variable, (f, a) = application.
Head machine on lists (top first): [a, b, c] ++ R  ->  ch(a) ++ [c, b.c] ++ R, where ch(a) are the spine
arguments of a (a must have head S; if a's head is a variable the run is STUCK: it would need to inspect
an opaque value).  hnf = list of length <= 2.
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(100000)

def app(*xs):
    t = xs[0]
    for x in xs[1:]:
        t = (t, x)
    return t

def spine(t):
    args = []
    while isinstance(t, tuple):
        args.append(t[1]); t = t[0]
    args.reverse()
    return t, args            # head (str), args

def build(head, args):
    t = head
    for a in args:
        t = (t, a)
    return t

def show(t):
    h, args = spine(t)
    s = h
    for a in args:
        s += (a if isinstance(a, str) and len(a) == 1 else "(" + show(a) + ")") if not (isinstance(a, str) and a == "S") else "S"
    return s

def parse(s):
    """S-terms with single-letter variables (lowercase except none reserved) and parentheses."""
    pos = [0]
    def atom():
        c = s[pos[0]]
        if c == "(":
            pos[0] += 1; t = term(); pos[0] += 1; return t
        pos[0] += 1
        return c
    def term():
        t = atom()
        while pos[0] < len(s) and s[pos[0]] != ")":
            t = (t, atom())
        return t
    return term()

def hnf(t, budget=200):
    """returns ('hnf', [comps]) | ('stuck', var, stack) | ('budget', stack)"""
    h, args = spine(t)
    if h != "S":
        return ("stuck", h, args)
    stack = list(args)               # top first
    steps = 0
    while len(stack) >= 3:
        if steps >= budget:
            return ("budget", stack)
        a, b, c = stack[0], stack[1], stack[2]
        ha, cha = spine(a)
        if ha != "S":
            return ("stuck", ha, stack)
        stack = list(cha) + [c, (b, c)] + stack[3:]
        steps += 1
    return ("hnf", stack, steps)

def size(t):
    return 1 if isinstance(t, str) else size(t[0]) + size(t[1])

def trees(n, memo={}):
    if n in memo: return memo[n]
    if n == 1:
        r = ["S"]
    else:
        r = [(l, rr) for i in range(1, n) for l in trees(i) for rr in trees(n - i)]
    memo[n] = r
    return r

def contains_var(t, v):
    if isinstance(t, str): return t == v
    return contains_var(t[0], v) or contains_var(t[1], v)

if __name__ == "__main__":
    # sanity: W_k Y -> S Y (W_{k-1} Y)
    r = hnf(app("S", "S", "w", "y"))
    print("SSwy ->", r[0], [show(c) for c in r[1]])
    r = hnf(app("S", app("S", "S"), "v", "y"))
    print("S(SS)vy ->", r[0], [show(c) for c in r[1]])
