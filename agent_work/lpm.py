"""Leftmost-path machine (LPM): state u (closed S-term) -> head-normalise u (head run until the list has < 3 elements)
-> next state = first component of the hnf (the frozen output is the second component).
Tools to iterate and to recognise states of the form  N_i . N_k . T  etc."""
import sys
import hm
SS = hm.parse("SS")
def hnf_list(u, budget=100000):
    a, h = hm.spine(u)
    assert h == 0
    st = list(reversed(a))
    s, k = hm.run(st, budget)
    return s, k, list(reversed(st))
def lpm_step(u, budget=100000):
    s, k, L = hnf_list(u, budget)
    if s != "hnf": return None, s, k, L
    if len(L) == 0: return None, "leaf", k, L
    return L[0], "ok", k, L
def nest(base, i, W=SS):
    t = base
    for _ in range(i): t = hm.app(W, t)
    return t
def iterate(u, n, budget=100000, show=None):
    out = []
    for j in range(n):
        nxt, st, k, L = lpm_step(u, budget)
        out.append((st, k, L))
        if show: print(j, st, k, show(u))
        if nxt is None: break
        u = nxt
    return out
if __name__ == "__main__":
    B = hm.parse("S(SS)(SS)")
    def dec(t):
        # decode a term X.Y.T with X, Y nests over B
        a, h = hm.spine(t)
        def nv(x):
            c = 0
            while x != B:
                aa, hh = hm.spine(x)
                if len(aa) == 2 and aa[0] == 0 and hm.app(0, 0) and x == hm.app(SS, aa[1]): c += 1; x = aa[1]
                else: return "?" + hm.show(x)[:20]
            return c
        return "[" + ", ".join(str(nv(x)) if True else "" for x in a) + "] head=" + hm.show(h) + " " + hm.show(t)[:60]
    u = hm.apps(nest(B, 2), nest(B, 1), 0)
    iterate(u, 12, show=dec)
