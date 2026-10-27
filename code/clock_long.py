"""Longer runs for clock candidates (main agent): head-spine sequence s(t) under parallel evaluation for t <= N; test
whether the differences are eventually periodic (period <= 40) on the second half."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
from parallel_eval import step_fn
P = step_fn()
N = int(sys.argv[1])
for src in sys.argv[2:]:
    W = hc.from_tuple(parse(src)); s = [len(hc.spine(W)[0])]
    for t in range(N):
        W = P(W); s.append(len(hc.spine(W)[0]))
    d = [b - a for a, b in zip(s, s[1:])]
    half = d[len(d) // 2:]
    per = next((p for p in range(1, 41) if len(half) > 2 * p and all(half[i] == half[i + p] for i in range(len(half) - p))), None)
    print(f"{src}: s(t) t={N - 9}..{N}: {s[-10:]}; differences eventually periodic: {('p=%d, slope %d/%d' % (per, sum(half[:per]), per)) if per else 'no (p <= 40)'}; DAG {len(hc.L)}", flush=True)
