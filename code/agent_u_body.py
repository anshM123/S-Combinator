"""Agent U, step 1: loop bodies for the SS-nest iterator.

With W = SS and N_m = (SS)^m B, two head steps give  N_m a b X1..Xp  ->  a b (N_{m-1} a b) X1..Xp.
So the iteration  N_m a b X  ->*  N_{m-1} a b X' J  holds for ALL m >= 1 iff the body F = a b satisfies,
with K opaque (K stands for N_{m-1} a b, which is never opened by the body except at its very end):
    F K X1..Xp  ->_head*  (front element K.Y)   with  Y ++ [d3, d2.d3] ++ rest  =  X' ++ junk
(the run reaches a list [K.Y, d2, d3, rest...] of length >= 3 whose front element is K-headed; opening it is the
next head step of the real run, and the real list is then ch(N_{m-1}) ++ [a, b] ++ Y ++ [d3, d2 d3] ++ rest).
This script searches small F, V and register formats X = (constants and the opaque counter M) for bodies with
X' = X[M := V M] (wrap increment) or X[M := M V] (append increment).  M is opaque: if the body opens M it fails.
Usage: python agent_u_body.py FMAX QMAX STEPS
"""
import sys, itertools
from symb import trees, show, spine, build

def step_run(lst, steps):
    """symbolic head machine on a list with opaque variables 'K','M'. Returns ('stuckK', list) or failure tag."""
    K = list(lst)
    for n in range(steps):
        if len(K) < 3: return ("hnf", K)
        a = K[0]
        h, aa = spine(a)
        if h == "K": return ("stuckK", K)
        if h != "S": return ("stuck" + h, K)
        b, c = K[1], K[2]
        K = list(aa) + [c, (b, c)] + K[3:]
    return ("budget", K)

def check(F, fmt, V, mode, steps):
    hF, chF = spine(F)
    if not chF: return None
    lst = list(chF) + ["K"] + list(fmt)
    tag, K = step_run(lst, steps)
    if tag != "stuckK": return None
    h, Y = spine(K[0])
    if len(K) < 3: return None
    regs = list(Y) + [K[2], (K[1], K[2])] + K[3:]
    inc = ("V", "M") if mode == "wrap" else ("M", "V")
    want = [ (V, "M") if (x == "M" and mode == "wrap") else (("M", V) if x == "M" else x) for x in fmt]
    if regs[:len(fmt)] == want:
        return regs
    return None

if __name__ == "__main__":
    FMAX, QMAX, STEPS = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    Fs = [t for n in range(2, FMAX + 1) for t in trees(n)]
    Qs = [t for n in range(1, QMAX + 1) for t in trees(n)]
    Vs = [t for n in range(1, QMAX + 1) for t in trees(n)]
    fmts = [["M"]]
    for q in Qs:
        fmts += [[q, "M"], ["M", q]]
    for q1, q2 in itertools.product(Qs, repeat=2):
        fmts += [[q1, q2, "M"], [q1, "M", q2], ["M", q1, q2]]
    hits = []
    for F in Fs:
        for fmt in fmts:
            for V in Vs:
                for mode in ("wrap", "append"):
                    r = check(F, fmt, V, mode, STEPS)
                    if r is not None:
                        hits.append((show(F), [show(x) if x != "M" else "M" for x in fmt], show(V), mode,
                                     [show(x) for x in r]))
    print("hits:", len(hits))
    for h in hits[:60]:
        print(h)
