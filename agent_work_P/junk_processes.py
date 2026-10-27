"""Junk as processes (agent_work_P, exploratory).  Under ReplaceAll every element below the window evolves on its own
(Lemma PJ), so junk pushed by a head run is a running process.  For a term t, run the leftmost-outermost head machine
(the skeleton, Theorem PT) for N steps; for every element pushed as the product b.c at step s, record h_par(b.c)
(its own ReplaceAll head-normalisation time, direct passes with a size cap; None = not within the caps).
Prints the step at which each product was pushed, the opcode at that step, and h_par.
Usage: python junk_processes.py TERM N"""
import sys
from ptools import *
src = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
def hpar(u, cap=200, maxsize=20000):
    for j in range(cap):
        if is_hnf(u): return j
        if size(u) > maxsize or len(hc.L) > 2_000_000: return None
        u = P(u)
    return None
t = T(src); stk = list(reversed(spine(t)[0])); rows = []
for s in range(N):
    if len(stk) < 3: break
    a = stk.pop(); b = stk.pop(); c = stk.pop()
    sa, h = spine(a)
    if h != 0: break
    bc = hc.app(b, c)
    rows.append((s, len(sa), size(bc), hpar(bc)))
    stk.append(bc); stk.append(c); stk.extend(reversed(sa))
for r in rows: print(r)
