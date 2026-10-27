"""Probe (agent_work_RR): normalisation times of the elements of Theorem PL's parallel loop.
D = S(SS), L = S D, C_1 = L, C_{i+1} = L C_i.  Elements C_{j-1}(C_2 C_j) etc."""
import sys
from nf_scan import hc, step_fn, reset, NODE_CAP
def npar(t, cap=20000):
    P = step_fn()
    for k in range(cap + 1):
        u = P(t)
        if u == t: return k
        t = u
        if len(hc.L) > NODE_CAP: return None
    return None
def ap(*xs):
    t = xs[0]
    for x in xs[1:]: t = hc.app(t, x)
    return t
for j in range(3, 16):
    reset()
    D = ap(0, ap(0, 0)); L = ap(0, D); C = [None, L]
    for i in range(1, j + 2): C.append(ap(L, C[-1]))
    e4 = ap(C[j - 1], ap(C[2], C[j]))
    print(j, "n_par(C_{j-1}(C_2 C_j)) =", npar(e4), " n_par(C_j C_j S) =", npar(ap(C[j], C[j], 0)), " n_par(C_j S)=", npar(ap(C[j], 0)))
