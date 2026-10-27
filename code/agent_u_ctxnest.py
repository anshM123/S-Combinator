"""Agent U: exact symbolic head machine for counters with arbitrary LAYER CONTEXTS (round 2).

A family f = (ctx, base): ctx is a closed term with exactly one hole '#', the counter value n is ctx^n[base].
Symbolic element ('C', f, var, off) = value (var + off) of family f (var a counter name, constraints in Br).
Opening a symbolic counter case-splits: value 0 -> spine(base); value >= 1 -> spine(ctx[ ('C', f, var, off-1) ]).
fold() rewrites every subterm ctx[('C', f, v, o)] into ('C', f, v, o+1) (bottom-up), and base into ('C', f, None, 0)
is NOT done (constants stay constants).  Opaque variables (strings other than 'S') are never opened.
explore(): template search inside one head run: start list, run with case splits, report every later configuration
whose prefix matches a template pattern.
"""
import sys
sys.setrecursionlimit(100000)
from symb import spine as tspine

def isC(e): return isinstance(e, tuple) and len(e) == 4 and e[0] == "C"

def plug(ctx, x):
    if ctx == "#": return x
    if isinstance(ctx, str): return ctx
    return (plug(ctx[0], x), plug(ctx[1], x))

def spine(t):
    args = []
    while isinstance(t, tuple) and not isC(t):
        args.append(t[1]); t = t[0]
    args.reverse(); return t, args

class Br:
    def __init__(self, cons): self.cons = dict(cons)
    def get(self, v): return self.cons.get(v, ("ge", 0))
    def can_zero(self, v, d):
        c = self.get(v); return (c[1] + d == 0) if c[0] == "eq" else (c[1] <= -d)
    def can_pos(self, v, d):
        c = self.get(v); return (c[1] + d >= 1) if c[0] == "eq" else True
    def set_zero(self, v, d):
        b = Br(self.cons); b.cons[v] = ("eq", -d); return b
    def set_pos(self, v, d):
        b = Br(self.cons); c = self.get(v)
        if c[0] == "ge": b.cons[v] = ("ge", max(c[1], 1 - d))
        return b

def open_el(e, fams, br):
    """list of (pushed list, branch); None if the head is an opaque variable"""
    h, args = spine(e)
    if isinstance(h, str):
        if h != "S": return None
        return [(list(args), br)]
    _, f, v, d = h
    ctx, base = fams[f]
    out = []
    if br.can_zero(v, d):
        out.append((list(tspine(base)[1]) + list(args), br.set_zero(v, d)))
    if br.can_pos(v, d):
        inner = plug(ctx, ("C", f, v, d - 1))
        out.append((list(spine(inner)[1]) + list(args), br.set_pos(v, d)))
    return out

def match_ctx(t, ctx):
    """if t = ctx[C] with C a counter element, return C"""
    if ctx == "#": return t if isC(t) else None
    if isinstance(ctx, str): return None if t != ctx else False
    if not isinstance(t, tuple) or isC(t): return None
    a = match_ctx(t[0], ctx[0]); b = match_ctx(t[1], ctx[1])
    if a is None or b is None: return None
    if a is False: return b
    if b is False: return a
    return None

def fold(t, fams):
    if isinstance(t, str) or isC(t): return t
    t = (fold(t[0], fams), fold(t[1], fams))
    for f, (ctx, base) in enumerate(fams):
        c = match_ctx(t, ctx)
        if c not in (None, False) and c[1] == f:
            return ("C", f, c[2], c[3] + 1)
    return t

def run(start, fams, stop, maxsteps=200, cap=6):
    """stop(K, br, n) -> label or None. Returns list of (constraints, label, steps)."""
    out = []; work = [(list(start), Br({}), 0)]
    while work:
        K, br, n = work.pop()
        if n > 0:
            lab = stop(K, br, n)
            if lab is not None: out.append((dict(br.cons), lab, n)); continue
        if n >= maxsteps: out.append((dict(br.cons), "budget", n)); continue
        if len(K) < 3: out.append((dict(br.cons), "hnf", n)); continue
        if any(c[1] > cap for c in br.cons.values()): out.append((dict(br.cons), "cap", n)); continue
        r = open_el(K[0], fams, br)
        if r is None: out.append((dict(br.cons), "stuck:" + str(spine(K[0])[0]), n)); continue
        for (l, b2) in r:
            work.append(([fold(x, fams) for x in l + [K[2], (K[1], K[2])]] + K[3:], b2, n + 1))
    return out

if __name__ == "__main__":
    # self-test 1: sawtooth (ctx SS#, base S(SS)(SS)); node N_i N_k S as the front element over opaque tape
    SS = ("S", "S"); B = (("S", SS), SS)
    fams = [((SS, "#"), B)]
    node = ((("C", 0, "i", 0), ("C", 0, "k", 0)), "S")
    def stop(K, br, n):
        h, a = spine(K[0])
        if isC(h) and len(a) == 2 and isC(a[0]) and a[1] == "S": return (h[2:], a[0][2:])
        return None
    print("sawtooth:", run([node, "w1", "w2"], fams, stop))
    # self-test 2: agent-U head-style transfer, ctx_P = S(S#)V2 ... P_k = S(S(S(S P)V1))V2 ; M ctx = SSq(S#)
    q = SS; V1 = ("S", "S", ) and (("S", "S"), q); V2 = "S"
    ctxP = ((("S", ("S", ((("S", ("S", "#")), V1)))), V2))
    ctxM = (((("S", "S"), q)), ("S", "#"))
    B1 = (("S", ("S", ("S", "S"))), (("S", ("S", ("S", "S"))), "S"))   # placeholder base (not opened for i >= 1)
    fams2 = [(ctxP, B1), (ctxM, ("S", ("S", "S")))]
    def stop2(K, br, n):
        if isC(K[0]) and K[0][1] == 0 and len(K) > 2 and isC(K[2]) and K[2][1] == 1: return (K[0][2:], K[2][2:])
        return None
    print("transfer R1:", [o for o in run([("C", 0, "k", 0), "x", ("C", 1, "m", 0), "w1"], fams2, stop2, maxsteps=10)])
