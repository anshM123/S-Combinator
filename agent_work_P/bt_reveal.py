"""Timed Boehm trees under ReplaceAll (agent_work_P, exploratory).  For a term t, the node of the Boehm tree at path w
(0 = first, 1 = second argument of a head normal form S a b; S a has only child 0) is revealed at the first pass at which
the subterm there is head-normal.  By Lemma LZ (ii) the two arguments of a head normal form evolve independently, so
  tau(child) = tau(parent) + h_par(child as it is at pass tau(parent)).
This script computes tau on all nodes up to depth D (direct passes, size cap) and prints, per node, the increment
tau(child) - tau(parent) together with the increment the child WOULD have needed had it not been pre-evaluated
(h_par of the child as first created is not available here, so we report h_LO of the child as found, for contrast).
Usage: python bt_reveal.py TERM D"""
import sys
from ptools import *
sys.setrecursionlimit(100000)
CAP = 200000
def hpar(u, cap=400):
    for j in range(cap):
        if is_hnf(u): return j, u
        if size(u) > CAP: return None, u
        u = P(u)
    return None, u
rows = []
def walk(u, tau, w, D):
    j, v = hpar(u)
    if j is None: rows.append((w, None, None)); return
    rows.append((w, tau + j, j))
    if len(w) >= D: return
    a, h = spine(v)
    if h != 0: return
    for i, c in enumerate(a):
        walk(c, tau + j, w + str(i), D)
src = sys.argv[1]; D = int(sys.argv[2]) if len(sys.argv) > 2 else 6
walk(T(src), 0, '', D)
for w, tau, inc in rows[:200]:
    print(f"{w or 'root':10s} tau={tau} inc={inc}")
print('nodes', len(rows), 'unrevealed (no hnf within cap)', sum(1 for r in rows if r[1] is None))
