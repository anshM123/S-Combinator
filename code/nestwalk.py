"""Attempt U: exact counter programs of leftmost Böhm-tree walks on nest families.

A nest N(w, b, x, d) denotes W^{x+d}(B) for a symbolic counter x (or a constant when x is None); W is a wrapper term
W = S.[w1..wr] so that W y = S w1 .. wr y. Opening N with value 0 gives the spine of B, otherwise [w1, .., wr, N(.., d-1)].
The head machine runs on configurations of such objects with case splits on counters (constraints = lower bounds /
exact values). The leftmost walk descends into the first component. Composite W-applications to nests are folded back
into nests, so a child of the form (N(W,B,.) N(W,B,.)) R is recognised and gives an exact guarded transition.
Usage: python nestwalk.py   (runs the search over small wrappers / bases / tails)
"""
import sys, itertools, collections
sys.setrecursionlimit(100000)
from symb import trees, show, spine as sspine

MAXSTEPS = 400
CAP = 4

def spine(t):
    args = []
    while isinstance(t, tuple) and t[0] != "N":
        args.append(t[1]); t = t[0]
    args.reverse(); return t, args

class Br:
    """a branch: constraints on counters"""
    def __init__(self, cons):
        self.cons = dict(cons)          # var -> ("ge", n) or ("eq", n)
    def val_known(self, x, d):
        c = self.cons.get(x, ("ge", 0))
        if c[0] == "eq": return c[1] + d
        return None
    def can_zero(self, x, d):
        c = self.cons.get(x, ("ge", 0))
        return (c[1] + d == 0) if c[0] == "eq" else (c[1] <= -d)
    def can_pos(self, x, d):
        c = self.cons.get(x, ("ge", 0))
        return (c[1] + d >= 1) if c[0] == "eq" else True
    def set_zero(self, x, d):
        b = Br(self.cons); b.cons[x] = ("eq", -d); return b
    def set_pos(self, x, d):
        b = Br(self.cons); c = self.cons.get(x, ("ge", 0))
        if c[0] == "ge": b.cons[x] = ("ge", max(c[1], 1 - d))
        return b

def open_el(e, W, B, br):
    """list of (elements, branch)"""
    if e == "S": return [([], br)]
    if isinstance(e, tuple) and e[0] == "N":
        _, wi, bi, x, d = e
        out = []
        if x is None:
            if d == 0: out.append((sspine(B[bi])[1], br))
            else: out.append((sspine(W[wi])[1] + [("N", wi, bi, None, d - 1)], br))
            return out
        if br.can_zero(x, d): out.append((sspine(B[bi])[1], br.set_zero(x, d)))
        if br.can_pos(x, d): out.append((sspine(W[wi])[1] + [("N", wi, bi, x, d - 1)], br.set_pos(x, d)))
        return out
    f, a = e
    return [(l + [a], b2) for (l, b2) in open_el(f, W, B, br)]

def hnf(K, W, B, br):
    """run the head machine; list of (final configuration, branch) or ('budget', ...)"""
    out = []; work = [(K, br, 0)]
    while work:
        K, br, n = work.pop()
        if len(K) < 3: out.append((K, br)); continue
        if n > MAXSTEPS or any(v[1] > CAP for v in br.cons.values()): out.append((None, br)); continue
        a, b, c = K[0], K[1], K[2]
        for (l, b2) in open_el(a, W, B, br):
            work.append((l + [c, (b, c)] + K[3:], b2, n + 1))
    return out

def fold(t, W):
    """fold W-applications to nests back into nests: (S w1 .. wr) N(...) -> N(..., d+1)"""
    if t == "S" or (isinstance(t, tuple) and t[0] == "N"): return t
    f, a = fold(t[0], W), fold(t[1], W)
    if isinstance(a, tuple) and a and a[0] == "N":
        h, args = spine(f) if isinstance(f, tuple) else (f, [])
        wi = a[1]
        if h == "S" and args == sspine(W[wi])[1]:
            return ("N", a[1], a[2], a[3], a[4] + 1)
    return (f, a)

def walk_template(W, B, R, bi1, bi2, steps=12):
    """node T(i,k) = (N(0,bi1,i,0) N(0,bi2,k,0)) R ; follow the leftmost walk until the node matches
    (N(0,bi1,.) N(0,bi2,.)) R again; return list of (constraints, transition or outcome)"""
    start = ((("N", 0, bi1, "i", 0), ("N", 0, bi2, "k", 0)), R)
    res = []
    work = [(start, Br({}), 0)]
    while work:
        node, br, n = work.pop()
        if n > 0:
            m = match(node, R, bi1, bi2)
            if m is not None:
                res.append((dict(br.cons), ("T", m, n))); continue
        if n >= steps: res.append((dict(br.cons), ("open", n))); continue
        conf_br = open_el(node, W, B, br)
        for (K0, b0) in conf_br:
            for (Kf, b1) in hnf(K0, W, B, b0):
                if Kf is None: res.append((dict(b1.cons), ("bottom?", n))); continue
                if not Kf: res.append((dict(b1.cons), ("leaf", n))); continue
                work.append((fold(Kf[0], W), b1, n + 1))
    return res

def match(node, R, bi1, bi2):
    if not (isinstance(node, tuple) and node[0] != "N"): return None
    if node[1] != R: return None
    p = node[0]
    if not (isinstance(p, tuple) and p[0] != "N"): return None
    a, b = p
    if isinstance(a, tuple) and a[0] == "N" and isinstance(b, tuple) and b[0] == "N" and a[1] == 0 and b[1] == 0 \
            and a[2] == bi1 and b[2] == bi2:
        return ((a[3], a[4]), (b[3], b[4]))
    return None

if __name__ == "__main__":
    W = [("S", "S")]                                   # wrapper SS: W y = S S y
    pool = [t for n in range(1, 6) for t in trees(n)]
    Rs = [t for n in range(1, 4) for t in trees(n)]
    found = []
    B = pool
    for bi1, bi2 in itertools.product(range(len(pool)), repeat=2):
        for R in Rs:
            res = walk_template(W, B, R, bi1, bi2)
            kinds = collections.Counter(r[1][0] for r in res)
            if kinds["T"] >= 2:
                found.append((show(pool[bi1]), show(pool[bi2]), show(R), [(c, r[1]) for c, r in res]))
    print(f"closed two-counter families with >= 2 guarded transitions: {len(found)}")
    for f in found[:25]:
        print("  B1 =", f[0], " B2 =", f[1], " R =", f[2])
        for c, tr in f[3]:
            print("      ", c, "->", tr)
