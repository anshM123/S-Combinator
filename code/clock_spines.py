"""Spine-length sequences of clocks under parallel evaluation (main agent): for every S-term W <= NMAX leaves that does
not normalise within N passes, s(t) = head-spine length of P^t(W), t = 0..N. Classified on t >= 20 as constant,
periodic (period <= 12), linear (constant difference), linear with periodic differences, or other."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import trees, show
import hc
from parallel_eval import step_fn
NMAX, N = int(sys.argv[1]), int(sys.argv[2])
P = step_fn()
def classify(s):
    t = s[20:]
    if len(set(t)) == 1: return f"constant {t[0]}"
    for p in range(1, 13):
        if all(t[i] == t[i + p] for i in range(len(t) - p)): return f"periodic p={p}"
    d = [b - a for a, b in zip(t, t[1:])]
    if len(set(d)) == 1: return f"linear slope {d[0]}"
    for p in range(2, 13):
        if all(d[i] == d[i + p] for i in range(len(d) - p)): return f"linear, periodic diffs p={p} (slope {sum(d[:p])}/{p})"
    return "other"
res = collections.defaultdict(list)
for n in range(1, NMAX + 1):
    for tt in trees(n):
        W = hc.from_tuple(tt); s = [len(hc.spine(W)[0])]; nf = False
        for k in range(N):
            u = P(W)
            if u == W: nf = True; break
            W = u; s.append(len(hc.spine(W)[0]))
        if nf: continue
        res[classify(s)].append((show(tt), s[20:32]))
for k in sorted(res, key=lambda k: -len(res[k])):
    print(f"{k}: {len(res[k])}  e.g. {res[k][0]}")
