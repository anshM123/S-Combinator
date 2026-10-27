"""Search for a transfer pass (A--, B++) in head runs over STACK templates (all interleavings of two counters and closed
'fuel' constants), exact and symbolic in the counter values.

Template: m slots, two of them counters A = N(WA, BA, i), B = N(WB, BB, k) (nests W^n(base), symbolic n), the others
closed constants; below them an opaque tape x1 x2 ... (never opened: a branch that opens a variable is dropped).
The symbolic head machine (case split n = 0 / n >= 1 when a nest is opened; W-applications folded back into nests)
runs until the first m list elements match the template again (same constants, same counter families in the same
slots); the guarded transition (i, k) -> (i', k') is recorded. Reports templates with a pass i -> i-1, k -> k+c (c >= 1).
Usage: python stacktransfer.py M CONSTMAX WRAPMAX BASEMAX STEPS
"""
import sys, itertools, collections
sys.setrecursionlimit(100000)
from symb import trees, show
from nestwalk import Br

def fold(t, W):
    """fold W-applications to nests back into nests; strings (S, tape variables) and nests are atoms"""
    if isinstance(t, str) or t[0] == "N": return t
    f, a = fold(t[0], W), fold(t[1], W)
    if isinstance(a, tuple) and a[0] == "N":
        h, args = sspine(f)
        if h == "S" and args == sspine(W[a[1]])[1]:
            return ("N", a[1], a[2], a[3], a[4] + 1)
    return (f, a)

M, CONSTMAX, WRAPMAX, BASEMAX, STEPS = (int(a) for a in sys.argv[1:6])
CAP, MAXLEN = 3, 40

def sspine(t):
    args = []
    while isinstance(t, tuple) and t[0] != "N":
        args.append(t[1]); t = t[0]
    args.reverse(); return t, args

def open_el(e, W, B, br):
    """children of the front element under each branch; None marks a variable head"""
    h, args = sspine(e)
    if h == "S": return [(args, br)]
    if isinstance(h, str): return None                      # opaque tape variable
    _, wi, bi, x, d = h
    out = []
    if x is None:
        out.append(((sspine(B[bi])[1] if d == 0 else sspine(W[wi])[1] + [("N", wi, bi, None, d - 1)]) + args, br))
        return out
    if br.can_zero(x, d): out.append((sspine(B[bi])[1] + args, br.set_zero(x, d)))
    if br.can_pos(x, d): out.append((sspine(W[wi])[1] + [("N", wi, bi, x, d - 1)] + args, br.set_pos(x, d)))
    return out

def match(K, tmpl):
    if len(K) < len(tmpl): return None
    res = {}
    for e, s in zip(K, tmpl):
        if s[0] == "J": continue                           # wildcard (junk) slot
        if s[0] == "C":
            if e != s[1]: return None
        else:
            if not (isinstance(e, tuple) and e[0] == "N" and e[1] == s[1] and e[2] == s[2]): return None
            if e[3] is None: return None
            res[s[0]] = (e[3], e[4])
    return res

def transitions(tmpl, W, B):
    K0 = []
    for j, s in enumerate(tmpl):
        if s[0] == "J": K0.append("j%d" % j); continue
        K0.append(s[1] if s[0] == "C" else ("N", s[1], s[2], "i" if s[0] == "A" else "k", 0))
    K0 += ["x1", "x2", "x3", "x4"]
    out = []; work = [(K0, Br({}), 0)]
    while work:
        K, br, n = work.pop()
        if n > 0:
            m = match(K, tmpl)
            if m is not None: out.append((dict(br.cons), m, n)); continue
        if n >= STEPS or len(K) < 3 or len(K) > MAXLEN or any(v[1] > CAP for v in br.cons.values()): continue
        r = open_el(K[0], W, B, br)
        if r is None: continue
        for (l, b2) in r:
            newK = [fold(e, W) for e in (l + [K[2], (K[1], K[2])])] + K[3:]
            work.append((newK, b2, n + 1))
    return out

if __name__ == "__main__":
    consts = ["*"] + [t for n in range(1, CONSTMAX + 1) for t in trees(n)]
    wraps = [t for n in range(2, WRAPMAX + 1) for t in trees(n)]
    bases = [t for n in range(1, BASEMAX + 1) for t in trees(n)]
    hits = []; kinds = collections.Counter(); ntmpl = 0
    for posA, posB in itertools.permutations(range(M), 2):
        others = [p for p in range(M) if p not in (posA, posB)]
        for cs in itertools.product(range(len(consts)), repeat=len(others)):
            for wa, wb in itertools.product(range(len(wraps)), repeat=2):
                W = [wraps[wa], wraps[wb]]
                for ba, bb in itertools.product(range(len(bases)), repeat=2):
                    B = [bases[ba], bases[bb]]
                    tmpl = [None] * M
                    tmpl[posA] = ("A", 0, 0); tmpl[posB] = ("B", 1, 1)
                    for p, ci in zip(others, cs): tmpl[p] = ("J",) if consts[ci] == "*" else ("C", consts[ci])
                    ntmpl += 1
                    for cons, m, n in transitions(tmpl, W, B):
                        a, b = m.get("A"), m.get("B")
                        if a is None or b is None: continue
                        kinds[(a, b)] += 1
                        if a == ("i", -1) and b[0] == "k" and b[1] >= 1:
                            hits.append((tmpl, show(W[0]), show(W[1]), show(B[0]), show(B[1]), cons, n, b))
    print(f"templates {ntmpl}; transition kinds (top): {kinds.most_common(12)}")
    print(f"transfer passes (A-1, B+c): {len(hits)}")
    for h in hits[:20]:
        tm = [s[0] if s[0] in "ABJ" else show(s[1]) for s in h[0]]
        print("  tmpl", tm, "WA", h[1], "WB", h[2], "BA", h[3], "BB", h[4], "guard", h[5], "steps", h[6], "B->", h[7])
