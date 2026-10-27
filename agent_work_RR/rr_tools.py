"""Tools for the race-material agent (agent_work_RR, 2026-10-27).
Exact ReplaceAll machinery = code/lazy_par.py (Lemma LZ; checked against direct passes, PROOF.md E96).
Conventions: a list [e1, e2, ...] is the term S e1 e2 ...; head step [a,b,c]++R -> ch(a)++[c, b.c]++R;
h_par(t) = first n with P^n(t) head-normal (spine length <= 2); h_lo(t) = number of head steps to an hnf.
Memory guard: every computation stops (raises Cap) beyond NODE_CAP hash-consed nodes.
"""
import sys, os
sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "code"))
import lazy_par as LP
from symb import parse

NODE_CAP = 2_000_000
class Cap(Exception):
    pass

S = 0
def ap(*xs):
    t = xs[0]
    for x in xs[1:]: t = LP.app(t, x)
    return t
def T(src):
    return LP.from_tuple(parse(src))
def comb(n):
    """left comb S S ... S with n leaves"""
    t = S
    for _ in range(n - 1): t = LP.app(t, S)
    return t
def num(n):
    """S-numeral n-bar = (SS.)^(n-1) SS  (n >= 1)"""
    assert n >= 1
    t = ap(S, S)
    for _ in range(n - 1): t = ap(S, S, t)
    return t
def show(t):
    return LP.show(LP.canon(t)) if t > 0 and LP.KIND[t] == 2 else LP.show(t)
def guard():
    if len(LP.KIND) > NODE_CAP: raise Cap(len(LP.KIND))

def hpar(t, cap=10**5):
    """ReplaceAll head-normalisation time of t (None if > cap passes)"""
    if t == S or len(LP.plain_spine(t)) < 3: return 0
    for k in range(1, cap + 1):
        if len(LP.force(t, k)) < 3: return k
        if k % 64 == 0: guard()
    return None
def par_list(t, k):
    """argument list of P^k(t) (elements may be DEL nodes: use show/canon)"""
    return LP.force(t, k)

def hlo(t, cap=10**6):
    """leftmost-outermost head steps to an hnf (None if > cap)"""
    stk = list(reversed(LP.plain_spine(t)))       # top last
    for n in range(cap + 1):
        if len(stk) < 3: return n
        a, b, c = stk.pop(), stk.pop(), stk.pop()
        ch = LP.plain_spine(a)
        stk.append(LP.app(b, c)); stk.append(c); stk.extend(reversed(ch))
        if n % 4096 == 0: guard()
    return None
def lo_list(t, n):
    stk = list(reversed(LP.plain_spine(t)))
    for _ in range(n):
        if len(stk) < 3: break
        a, b, c = stk.pop(), stk.pop(), stk.pop()
        ch = LP.plain_spine(a)
        stk.append(LP.app(b, c)); stk.append(c); stk.extend(reversed(ch))
    return list(reversed(stk))

def is_normal(t, memo={}):
    if t <= 0: return True
    r = memo.get(t)
    if r is None:
        if LP.KIND[t] == 2: t2 = LP.canon(t); r = is_normal(t2); memo[t] = r; return r
        args = []
        x = t
        while x > 0 and LP.KIND[x] == 1: args.append(LP.B[x]); x = LP.A[x]
        r = (x == 0 and len(args) <= 2 or x < 0) and all(is_normal(a) for a in args)
        memo[t] = r
    return r

def fit_poly2(data, deg=2):
    """least-squares-free exact fit: data = {(n, m): value}; find integer-free rational coefficients of monomials n^i m^j
    (i + j <= deg) by solving on a subset and verifying on all.  Returns (coeffs dict, ok)."""
    from fractions import Fraction
    mons = [(i, j) for i in range(deg + 1) for j in range(deg + 1 - i)]
    pts = sorted(data)
    # pick points greedily to get an invertible system
    import itertools
    rows = []; vals = []; chosen = []
    def rank(M):
        M = [r[:] for r in M]; rk = 0; cols = len(M[0]) if M else 0
        for c in range(cols):
            piv = next((r for r in range(rk, len(M)) if M[r][c] != 0), None)
            if piv is None: continue
            M[rk], M[piv] = M[piv], M[rk]
            for r in range(len(M)):
                if r != rk and M[r][c] != 0:
                    f = M[r][c] / M[rk][c]; M[r] = [a - f * b for a, b in zip(M[r], M[rk])]
            rk += 1
        return rk
    for p in pts:
        row = [Fraction(p[0]) ** i * Fraction(p[1]) ** j for i, j in mons]
        if rank(rows + [row]) > len(rows):
            rows.append(row); vals.append(Fraction(data[p])); chosen.append(p)
        if len(rows) == len(mons): break
    if len(rows) < len(mons): return None, False
    # solve
    n = len(mons); M = [rows[i][:] + [vals[i]] for i in range(n)]
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c] != 0); M[c], M[piv] = M[piv], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]; M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    co = {mons[i]: M[i][n] / M[i][i] for i in range(n)}
    ok = all(sum(co[(i, j)] * Fraction(p[0]) ** i * Fraction(p[1]) ** j for i, j in mons) == data[p] for p in pts)
    return {k: v for k, v in co.items() if v != 0}, ok
