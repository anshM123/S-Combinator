"""Leftmost-innermost (call-by-value) evolution of S-terms (main agent, 2026-10-26).
LI step on t = S a1 … an: if one of a1, a2, a3 (those present) contains a redex, step inside the first such argument;
else, if n >= 3, contract the head (S a1 a2 a3 is then innermost and leftmost); else t is a normal form.
For each non-normalising term up to N leaves this records, per step, the depth of the contracted redex (number of
argument descents from the root) and reports how that depth behaves: the suffix minimum of the depth is the depth of
the part of the term that never changes again (frozen context).
Usage: python li_explore.py NMAX STEPS"""
import sys, itertools, collections
sys.setrecursionlimit(1000000)
import hc

_red = {}
def has_redex(i):
    if i <= 0: return False
    r = _red.get(i)
    if r is None:
        args, h = hc.spine(i)
        r = (h == 0 and len(args) >= 3) or any(has_redex(a) for a in args)
        _red[i] = r
    return r

def build(h, args):
    t = h
    for a in args: t = hc.app(t, a)
    return t

def li_step(i):
    """one leftmost-innermost step: (new term, depth of the contracted redex) or None for a normal form"""
    path = []                                   # (head, args, k): rebuild after the step
    while True:
        args, h = hc.spine(i)
        k = next((k for k in range(min(3, len(args))) if has_redex(args[k])), None)
        if k is not None:
            path.append((h, args, k)); i = args[k]; continue
        if len(args) < 3: return None if not path else None   # cannot happen when a redex was found above
        new = hc.app(hc.app(args[0], args[2]), hc.app(args[1], args[2]))
        for x in args[3:]: new = hc.app(new, x)
        break
    d = len(path)
    for h, args, k in reversed(path):
        a2 = list(args); a2[k] = new; new = build(h, a2)
    return new, d

def terms(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in terms(k):
            for r in terms(n - k): yield hc.app(l, r)

def show(i): return hc.show(i)

_sz = {}
def tsize(i):
    """leaf count with a memo that is cleared together with the term tables (hc.size keeps a global memo across resets)"""
    if i <= 0: return 1
    r = _sz.get(i)
    if r is None:
        r = tsize(hc.L[i]) + tsize(hc.R[i]); _sz[i] = r
    return r

if __name__ == "__main__":
    NMAX, STEPS = int(sys.argv[1]), int(sys.argv[2])
    tally = collections.Counter(); examples = collections.defaultdict(list)
    for n in range(3, NMAX + 1):
        srcs = [show(t) for t in terms(n)]
        for src in srcs:
            hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear(); _red.clear(); _sz.clear()     # fresh tables per term (memory)
            from symb import parse
            t = hc.from_tuple(parse(src))
            if not has_redex(t): continue
            u = t; depths = []; sizes = []
            for s in range(STEPS):
                r = li_step(u)
                if r is None: break
                u, d = r; depths.append(d)
                if s % 20 == 0 and tsize(u) > 200000: break
            if len(depths) < STEPS and li_step(u) is None:
                tally["normalises"] += 1; continue
            h = len(depths); m2 = min(depths[h // 2:]); m4 = min(depths[3 * h // 4:]); mx = max(depths)
            kind = "frozen depth grows" if m4 > m2 else "frozen depth stable"
            tally[kind] += 1
            if len(examples[kind]) < 6: examples[kind].append((show(t), h, m2, m4, mx, depths[-12:]))
    for k, v in tally.items(): print(f"{k}: {v}")
    for k, ex in examples.items():
        print(k)
        for e in ex: print("   ", e)
