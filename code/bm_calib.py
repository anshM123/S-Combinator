"""Calibration and comparison for bm_sizes (main agent)."""
import sys, json
sys.setrecursionlimit(1000000)
from bm_sizes import bm
from symb import parse
import hc
from parallel_eval import step_fn, size
P = 1_000_000_007
fib = [1, 1]
for _ in range(118): fib.append(fib[-1] + fib[-2])
print("calibration: Fibonacci L =", bm(fib, P), "| Fibonacci + n^2:", bm([f + i * i for i, f in enumerate(fib)], P),
      "| 2^n + 3^n:", bm([2 ** i + 3 ** i for i in range(120)], P))
for src, N in (("S(SS)SSSS", 120), ("S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(SSS(SS))))", 70), ("SSS(S(SS))", 120), ("S(SSS)(SSS)", 120)):
    t = hc.from_tuple(parse(src)); s = [size(t)]
    for n in range(N):
        u = step_fn()(t)
        if u == t: break
        t = u; s.append(size(t))
    print(f"{src}: {len(s)} sizes, last {s[-1] if s[-1] < 10**12 else '%.3e' % s[-1]}; L = {bm(s, P)} (from n=20: {bm(s[20:], P)} of {len(s) - 20})")
