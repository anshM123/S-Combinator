"""Generalised Theorem BC2 coverage (main agent): for each uncovered census counter, look for a step at which the top three
are R'(M) = [M·(S·M), S·(M·(S·M)), (S·M)·(M·(S·M))] with M = (S L)(L (S L)) for some L (the BC2 scheme with an unknown
level L); collect the levels L seen, recover the base L_0 by unfolding L = S·((S L')(L' (S L'))), and check the base
cases: L_0 and L_1 (= S·M_0) return R'(x·y) on generic arguments without opening an atom. If so, the symbolic
derivation of Theorem BC2 (level tokens, base-independent) proves the run from that point on."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse, show
import hc
def M_of(L): return hc.app(hc.app(0, L), hc.app(L, hc.app(0, L)))
def as_M(t):
    """if t = (S L)(L (S L)) return L"""
    if t <= 0: return None
    f, a = hc.L[t], hc.R[t]
    if f <= 0 or hc.L[f] != 0: return None
    Lx = hc.R[f]
    return Lx if t == M_of(Lx) else None
def unfold(L):
    """if L = S·M_of(L') return L'"""
    if L <= 0 or hc.L[L] != 0: return None
    return as_M(hc.R[L])
SECOND = [0, hc.app(0, 0)]       # S·E (form R') or SS·E (form R'')
def R_of(Z, g=0):
    ZSZ = hc.app(Z, hc.app(0, Z)); return [ZSZ, hc.app(SECOND[g], ZSZ), hc.app(hc.app(0, Z), ZSZ)]
def returns_R(L0, g=0):
    X, Y = -1, -2; XY = hc.app(X, Y); stk = [-6, -5, -4, -3, Y, X, L0]
    for t in range(10000):
        a = stk[-1]; ch, h = hc.spine(a)
        if h != 0: return stk[-1:-4:-1] == R_of(XY, g), t
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return False, None
rows = [l.rstrip("\n").split("\t") for l in open("../data/lo_census2_12.tsv", encoding="utf-8") if "\t" in l]
res = collections.Counter(); bases = collections.Counter(); examples = {}
for cls_, src, *_ in rows:
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; levels = []
    for n in range(40000):
        if len(stk) < 3: break
        top = stk[-1:-4:-1]
        a = top[0]
        if a > 0:
            Mx = hc.L[a]; 
            for g in (0, 1):
                if hc.R[a] == hc.app(0, Mx) and as_M(Mx) is not None and top == R_of(Mx, g):
                    levels.append((n, as_M(Mx), g))
                if len(levels) >= 3: break
        stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    if len(levels) < 2: res[(cls_, "no BC2-scheme state")] += 1; continue
    L = levels[0][1]; g = levels[0][2]; chain = [L]
    while True:
        Lp = unfold(chain[-1])
        if Lp is None: break
        chain.append(Lp)
    L0 = chain[-1]; L1 = hc.app(0, M_of(L0))
    ok0, t0 = returns_R(L0, g); ok1, t1 = returns_R(L1, g)
    key = ("BC2 scheme (R'), base cases OK" if g == 0 else "BC2 scheme (R''), base cases OK") if ok0 and ok1 else "BC2 scheme, base cases FAIL"
    res[(cls_, key)] += 1
    if ok0 and ok1:
        bases[show_b := hc.size(L0)] += 0
        examples.setdefault(key, []).append((src, n, len(chain) - 1, t0, t1))
for k, v in sorted(res.items()): print(f"{k[0]:16s} {k[1]:30s} {v}")
for k, v in examples.items(): print(k, v[:5])
