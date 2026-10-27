"""Targeted search for a tag-like Böhm-tree step (full-read loophole).
Node: S C w1 ... wm E  (C control, E end marker, wi in {alpha, beta}).
Accept if for some fixed component index k and fixed closed prefix list P (same for all words):
  args(component_k) == P ++ [w2..wm] ++ [T(w1)]   (delete-1, copy rest, append something depending on w1),
or the deletion-2 variant P ++ [w3..wm] ++ [T(w1)], with T(alpha) != T(beta).
"""
import sys, itertools
from symb import *
G = [t for n in range(1, 5) for t in trees(n)]
def comps_of(t):
    r = hnf(t, budget=4 * size(t) + 200)
    return r[1] if r[0] == "hnf" else None
def check(C, a, b, E, words):
    pat = None   # (k, prefix tuple, deletion d) learned from first word, T-map learned per first symbol
    T = {}
    for w in words:
        syms = [a if x == 0 else b for x in w]
        cs = comps_of(app("S", C, *syms, E))
        if cs is None: return None
        ok_any = False
        cands = []
        for k, comp in enumerate(cs):
            h, args = spine(comp)
            for d in (1, 2):
                rest = syms[d:]
                n = len(rest)
                if len(args) < n + 1: continue
                pre = tuple(args[:len(args) - n - 1]); mid = args[len(args) - n - 1:len(args) - 1]; last = args[-1]
                if mid == rest:
                    cands.append((k, pre, d, last))
        if not cands: return None
        if pat is None:
            # keep all candidate patterns, filter by later words
            pat = [(k, pre, d) for (k, pre, d, last) in cands]
            for (k, pre, d, last) in cands:
                T.setdefault((k, pre, d, w[0]), last)
        else:
            newpat = []
            for (k, pre, d) in pat:
                for (k2, pre2, d2, last) in cands:
                    if (k2, pre2, d2) == (k, pre, d):
                        key = (k, pre, d, w[0])
                        if key in T and T[key] != last: continue
                        T.setdefault(key, last); newpat.append((k, pre, d))
            pat = newpat
        if not pat: return None
    # require T depends on first symbol
    good = [(k, pre, d) for (k, pre, d) in pat if T.get((k, pre, d, 0)) is not None and T.get((k, pre, d, 1)) is not None and T[(k, pre, d, 0)] != T[(k, pre, d, 1)]]
    return good or None
words = [w for m in range(3, 7) for w in itertools.product((0, 1), repeat=m)]
words.sort(key=len)
found = 0; tested = 0
for a in G:
    for b in G:
        if a == b: continue
        for C in G:
            for E in G:
                tested += 1
                g = check(C, a, b, E, words[:12])
                if g and check(C, a, b, E, words):
                    found += 1
                    print("FOUND C=%s alpha=%s beta=%s E=%s pattern=%s" % (show(C), show(a), show(b), show(E), g[:2])); sys.stdout.flush()
print("tested", tested, "found", found)
