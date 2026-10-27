"""Disprover: watch the reload loop (sawtooth) inside the head run of t z z, t = S(S(SS))(S(SS))(SS)S (E36 term).

Prints the top TOP stack elements every step, with SS-nests compressed: N<k>[x] = (SS)^k x (k >= 1 layers of SS
applied to x), variables z stay opaque. Usage: python sawview.py STEPS TOP
"""
import sys
from symb import parse, spine

sys.setrecursionlimit(100000)

def nestdepth(t):
    k = 0
    while isinstance(t, tuple) and t[0] == ("S", "S"):
        k += 1; t = t[1]
    return k, t

def sh(t):
    k, base = nestdepth(t)
    if k >= 1:
        return f"N{k}[{sh(base)}]"
    if isinstance(t, str):
        return t
    h, args = spine(t)
    return h + "".join(a if isinstance(a, str) else "(" + sh(a) + ")" for a in args)

def run(t, steps, top):
    h, K = spine(t); K = list(K)
    for n in range(steps):
        if len(K) < 3: print("hnf"); return
        a, b, c = K[0], K[1], K[2]
        ha, aa = spine(a)
        if ha != "S": print(n, "stuck on", ha); return
        print(f"{n:4d} len={len(K):3d} | " + " , ".join(sh(e) for e in K[:top]))
        K = list(aa) + [c, (b, c)] + K[3:]

if __name__ == "__main__":
    run(parse("S(S(SS))(S(SS))(SS)Szz"), int(sys.argv[1]), int(sys.argv[2]))
