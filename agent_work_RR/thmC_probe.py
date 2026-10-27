"""Probe: Theorem C data W_r = (SS.)^r K, K = S S N3 N1: do processes built from W_r normalise under ReplaceAll?"""
from nf_scan import hc, step_fn, reset
def ap(*xs):
    t = xs[0]
    for x in xs[1:]: t = hc.app(t, x)
    return t
def npar(t, cap=3000):
    P = step_fn()
    for k in range(cap + 1):
        u = P(t)
        if u == t: return k
        t = u
        if len(hc.L) > 1000000: return "cap"
    return None
for r in range(0, 6):
    reset()
    S = 0; N1 = ap(S, S); N3 = ap(S, ap(S, ap(S, S))); K = ap(S, S, N3, N1)
    W = K
    for _ in range(r): W = ap(S, S, W)
    print(r, "W S:", npar(ap(W, S)), " W S S:", npar(ap(W, S, S)), " W W S:", npar(ap(W, W, S)), " 3bar W S:", npar(ap(ap(S,S,ap(S,S,ap(S,S))), W, S)), " W 3bar S:", npar(ap(W, ap(S,S,ap(S,S,ap(S,S))), S)))
