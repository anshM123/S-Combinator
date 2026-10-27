"""Tools for the parallel-universality agent (agent_work_P, 2026-10-27).
Terms are hash-consed ints from code/hc.py (0 = S, atoms < 0 are normal/opaque).
P  = one ReplaceAll pass (code/parallel_eval.step_fn): contract every outermost redex S x y z -> x z (y z).
H  = one leftmost-outermost (head) step on the spine.
"""
import sys, os
sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "code"))
import hc
from symb import parse
from parallel_eval import step_fn
P = step_fn()

def T(src):
    """parse a string like 'S(SS)S' into a hash-consed term"""
    return hc.from_tuple(parse(src))

def app(*xs):
    t = xs[0]
    for x in xs[1:]: t = hc.app(t, x)
    return t

def spine(t):
    args, h = hc.spine(t)
    return args, h

def build(h, args):
    t = h
    for a in args: t = hc.app(t, a)
    return t

def is_hnf(t):
    """S, S a, S a b, or atom-headed"""
    args, h = hc.spine(t)
    return h != 0 or len(args) <= 2

def head_step(t):
    """one leftmost-outermost head step (t must have S head with >= 3 args)"""
    args, h = hc.spine(t)
    assert h == 0 and len(args) >= 3
    x, y, z = args[0], args[1], args[2]
    return build(hc.app(hc.app(x, z), hc.app(y, z)), args[3:])

def lo_step(t, memo=None):
    """one leftmost-outermost step on the whole term (reduce the leftmost-outermost redex anywhere); None if normal"""
    args, h = hc.spine(t)
    if h == 0 and len(args) >= 3:
        return head_step(t)
    # hnf: reduce inside the first non-normal argument, left to right
    for i, a in enumerate(args):
        r = lo_step(a)
        if r is not None:
            return build(h, args[:i] + [r] + args[i + 1:])
    return None

def h_par(t, cap=10**6):
    """first n with P^n(t) in hnf (parallel head-normalisation time), and that term"""
    for n in range(cap):
        if is_hnf(t): return n, t
        t = P(t)
    return None, t

def h_lo(t, cap=10**6):
    for n in range(cap):
        if is_hnf(t): return n, t
        t = head_step(t)
    return None, t

def size(t, memo={}):
    if t <= 0: return 1
    s = memo.get(t)
    if s is None:
        s = size(hc.L[t]) + size(hc.R[t]); memo[t] = s
    return s

def show(t):
    return hc.show(t)

def is_normal(t, memo={}):
    if t <= 0: return True
    r = memo.get(t)
    if r is None:
        args, h = hc.spine(t)
        r = (h != 0 or len(args) <= 2) and all(is_normal(a) for a in args)
        memo[t] = r
    return r

# tree calls (Theorem CA): SS, seq(A1..Ak) = S N1, Ni = S Ai N(i+1), Nk = Ak S
SS = None
def seq(*As):
    k = len(As)
    N = hc.app(As[-1], 0)
    for A in reversed(As[:-1]):
        N = app(0, A, N)
    return hc.app(0, N)

def level(k, m):
    """k-ary counter level P_m: P_0 = SS, P_{m+1} = seq(P_m, ..., P_m)"""
    L = hc.app(0, 0)
    for _ in range(m):
        L = seq(*([L] * k))
    return L
