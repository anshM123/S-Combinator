"""Structure of the clock S(SSS)S(SSS) under parallel evaluation (main agent): slope estimates, difference alphabet,
factor complexity of the difference word, and a balance test."""
import sys, json
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn
P = step_fn(); N = int(sys.argv[1])
W = hc.from_tuple(parse("S(SSS)S(SSS)")); s = [len(hc.spine(W)[0])]
for t in range(N):
    W = P(W); s.append(len(hc.spine(W)[0]))
json.dump(s, open("../data/clock_SSSS_spine.json", "w"))
d = [b - a for a, b in zip(s, s[1:])]
print("slope s(t)/t:", {t: round(s[t] / t, 5) for t in (100, 250, 500, 750, N)})
print("slope over second half:", round((s[N] - s[N // 2]) / (N - N // 2), 5), "| 1/sqrt(3) =", round(3 ** -0.5, 5))
import collections
print("difference values:", dict(collections.Counter(d[N // 2:])))
tail = d[N // 4:]
print("factor complexity of differences:", {m: len({tuple(tail[i:i + m]) for i in range(len(tail) - m + 1)}) for m in (1, 2, 4, 8, 16, 32, 64)})
for w in (10, 50, 100):
    sums = [sum(tail[i:i + w]) for i in range(len(tail) - w + 1)]
    print(f"window {w}: sums range {min(sums)}..{max(sums)}")
