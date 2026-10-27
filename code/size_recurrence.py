"""Exact linear recurrences for parallel-evaluation size sequences (main agent): find the smallest order k <= KMAX with
s_n = c_1 s_{n-1} + ... + c_k s_{n-k} + c_0 holding exactly for all n >= n0 (rational c, then verified)."""
import sys
from fractions import Fraction
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn, size
def sizes_of(src, N):
    t = hc.from_tuple(parse(src)); out = [size(t)]
    for n in range(N):
        u = step_fn()(t)
        if u == t: break
        t = u; out.append(size(t))
    return out
def solve(A, b):
    n = len(A); M = [row[:] + [bb] for row, bb in zip(A, b)]
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None: return None
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]; M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]
def fit(s, KMAX=10):
    for k in range(1, KMAX + 1):
        for n0 in range(k, len(s) - 2 * k - 6):
            rows = [[Fraction(s[n - i]) for i in range(1, k + 1)] + [Fraction(1)] for n in range(n0, n0 + k + 1)]
            rhs = [Fraction(s[n]) for n in range(n0, n0 + k + 1)]
            c = solve(rows, rhs)
            if c is None: continue
            if all(sum(c[i - 1] * s[n - i] for i in range(1, k + 1)) + c[k] == s[n] for n in range(n0, len(s))):
                return k, n0, c
    return None
if __name__ == "__main__":
    src, N = sys.argv[1], int(sys.argv[2])
    s = sizes_of(src, N)
    r = fit(s)
    print(src, f"({len(s)} sizes):", "no recurrence of order <= 10" if r is None else
          f"order {r[0]} from n = {r[1]}: s_n = " + " + ".join(f"{c}*s_(n-{i+1})" for i, c in enumerate(r[2][:-1])) + f" + {r[2][-1]}")
