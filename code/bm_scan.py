"""Linear complexity of parallel-evaluation size sequences for all S-terms with NMIN..NMAX leaves that do not reach a
normal form within N passes (main agent). L near N/2 = no short linear recurrence; small L = linear-recurrent sizes."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse, trees, show
import hc
from parallel_eval import step_fn, size
from bm_sizes import bm
NMIN, NMAX, N = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
P = 1_000_000_007
hist = collections.Counter(); maxL = []; lowL = []
for n in range(NMIN, NMAX + 1):
    for tt in trees(n):
        t = hc.from_tuple(tt); s = [size(t)]; nf = False
        for k in range(N):
            u = step_fn()(t)
            if u == t: nf = True; break
            t = u; s.append(size(t))
            if s[-1] > 10 ** 40: break
        if nf or len(s) < N // 2: continue
        tail = s[10:]
        L = bm(tail, P); m = (len(tail) + 1) // 2
        cls = "maximal" if L >= m - 1 else ("small (<=6)" if L <= 6 else "intermediate")
        hist[cls] += 1
        if cls == "maximal" and len(maxL) < 12: maxL.append(show(tt))
        if cls != "maximal" and len(lowL) < 12: lowL.append((show(tt), L, len(tail)))
print(f"{NMIN}..{NMAX} leaves, {N} passes: {dict(hist)}")
print("  maximal-L examples:", maxL)
print("  non-maximal examples (term, L, terms):", lowL)
