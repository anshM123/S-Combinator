"""Automatic exact proofs for loop head runs (main agent, 2026-10-26) — generalises comb_prover.py.

Observed in the 12-leaf census: opcode words D_1 B^(n+c_1) D_2 B^(n+c_2) ... D_q B^(n+c_q) D_1 B^(n+1+c_1) ... — loops
whose counts grow by one per cycle. The loops consume 'combs' F^m(X): a fixed context F (one or more holes) iterated m
times over a base X — a right comb lam·lam·...·X (F = lam·[]) or, e.g., a linked list whose every link refers to the next
link twice (F = S [] (S P c ([] ...))).

Proof method (everything symbolic, for all n >= n0 at once):
 * Patterns. Terms over S, opaque atoms and comb tokens T(F, X, b) := F^(n+b)(X) (n symbolic; F a concrete context whose
   holes are the atom HOLE, X concrete with X != F(_)). The cycle-start window W(n) is inferred by anti-unifying the
   concrete cycle-start states of consecutive cycles (where they differ, t2 = F(t1) with F = t2 with every occurrence of
   t1 replaced by a hole, if F is small) and checked on a third cycle; a second pass expresses every subterm pair that
   consists of consecutive members of an already found family by that family's token (coupled recurrences: an element
   built from another element's comb).
 * Engine. Head-machine steps on patterns; a token at the head of a spine is unfolded (F^(n+b)(X) = F(F^(n+b-1)(X)),
   valid for n >= 1-b, recorded in n0); a product equal to F(T(F, X, b)) folds to T(F, X, b+1). Below the window lies the
   unknown rest r, represented by junk atoms: if one of them reaches the first three positions the attempt fails (r is
   never read), and opening an opaque head fails.
 * Loop lemma (LB). A window A containing the loop variable V (as F^k(V)): if the engine takes A(F(O)) (O opaque) in L steps
   to a state whose first |A| elements are A(O), then A(F^m(X)) ++ r ->^(mL) A(X) ++ r' for every m, X, r (induction).
   Loops are recognised (a) when a list element is a token and one block preserves the window with it peeled once, or
   (b) by comparing the window with the one L steps earlier (every difference a token one lower, all of one family).
 * Cycle lemma (LC). From W(n) the engine (steps + loop jumps) reaches a loop start equal to M(n+1) up to j blocks of its
   own loop, where M(n) is an earlier loop start; nothing below the window is read, so M(n) ++ r ->* M(n+1) ++ r'.
 * Transient: the concrete run reaches W(n_1) with n_1 >= n0 (instance check). Independent numerical cross-check: at the
   predicted times the concrete state is an instance of M(n) and M(n+1), for every later cycle.
Then the run is forever the cycle with n increasing; the opcode word is u ∏_n u_0 B_1^(n+b_1) u_1 ... — morphic.
"""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
import hc

OPQ = -1
VAR = -50                                              # loop variable inside an abstracted window
HOLE = -51                                             # hole of a comb context F
JUNKS = [-99, -98, -97, -96, -95, -94, -93, -92]
JUNKSET = set(JUNKS)
FAMILIES = set()                                       # (F, X) of the comb tokens in use
FAIL = object(); MISSING = object()

class Fail(Exception):
    pass

def is_tok(x): return isinstance(x, tuple) and x[0] == "T"
def is_seg(x): return isinstance(x, tuple) and x[0] == "G"     # ("G", P, F, X, b): the list P(X) ++ P(F X) ++ ... (n+b groups)

def repl_atom(p, atom, v):
    """replace an atom inside a pattern by the pattern v"""
    if isinstance(p, int):
        if p == atom: return v
        if p <= 0 or not contains(p, atom): return p
        return pmk(repl_atom(hc.L[p], atom, v), repl_atom(hc.R[p], atom, v))
    if p[0] == "A": return pmk(repl_atom(p[1], atom, v), repl_atom(p[2], atom, v))
    return p

_cv = {}
def contains(p, atom):
    if isinstance(p, int):
        if p <= 0: return p == atom
        k = (p, atom)
        if k not in _cv: _cv[k] = contains(hc.L[p], atom) or contains(hc.R[p], atom)
        return _cv[k]
    if p[0] == "A": return contains(p[1], atom) or contains(p[2], atom)
    return False

def parts(p):
    if isinstance(p, int): return (hc.L[p], hc.R[p]) if p > 0 else None
    if p[0] == "A": return (p[1], p[2])
    return None

def match(F, p, bind):
    """p == F(v) for one v (all holes equal)? returns v (or FAIL)"""
    if F == HOLE:
        if bind is MISSING: return p
        return bind if p == bind else FAIL
    if F <= 0 or not contains(F, HOLE): return bind if p == F else FAIL
    if is_tok(p): return FAIL
    pp = parts(p)
    if pp is None: return FAIL
    bind = match(hc.L[F], pp[0], bind)
    if bind is FAIL: return FAIL
    return match(hc.R[F], pp[1], bind)

def pmk(x, y):
    """canonical product of two patterns: F(T(F, X, b)) folds to T(F, X, b+1)"""
    if isinstance(x, int) and isinstance(y, int): return hc.app(x, y)
    p = ("A", x, y)
    for F, X in FAMILIES:
        v = match(F, p, MISSING)
        if v is not FAIL and v is not MISSING and is_tok(v) and v[1] == F and v[2] == X: return ("T", F, X, v[3] + 1)
    return p

def fill(F, v, memo=None):
    """F with every hole replaced by the pattern v"""
    if memo is None: memo = {}
    if F == HOLE: return v
    if F <= 0 or not contains(F, HOLE): return F
    if F in memo: return memo[F]
    r = pmk(fill(hc.L[F], v, memo), fill(hc.R[F], v, memo)); memo[F] = r; return r

def subst(p, v, var=VAR):
    """replace the loop variable (default VAR) by the pattern v"""
    if isinstance(p, int):
        if p == var: return v
        if p <= 0 or not contains(p, var): return p
        return pmk(subst(hc.L[p], v, var), subst(hc.R[p], v, var))
    if p[0] == "A": return pmk(subst(p[1], v, var), subst(p[2], v, var))
    return p

def shift(p, d=1):
    """W(n) -> W(n+d): every token offset grows by d"""
    if isinstance(p, int): return p
    if p[0] == "T": return ("T", p[1], p[2], p[3] + d)
    if p[0] == "G": return ("G", tuple(shift(q, d) for q in p[1]), p[2], p[3], p[4] + d)
    return pmk(shift(p[1], d), shift(p[2], d))

def expand(items, n, limit):
    """the concrete list denoted by items (patterns and segments) at parameter n, first `limit` entries"""
    out = []
    for it in items:
        if len(out) >= limit: break
        if is_seg(it):
            _, P, F, X, b = it
            c = X
            for j in range(n + b):
                for q in P:
                    out.append(inst(subst(q, c), n))
                if len(out) >= limit: break
                c = fill(F, c)
        else:
            out.append(inst(it, n))
    return out[:limit]

def inst(p, n):
    if isinstance(p, int): return p
    if p[0] == "A": return hc.app(inst(p[1], n), inst(p[2], n))
    _, F, X, b = p
    if n + b < 0: raise Fail("negative token count")
    t = X
    for _ in range(n + b): t = fill(F, t)
    return t

def min_offset(p):
    """smallest token offset b in a pattern (the pattern denotes terms only for n >= -b)"""
    if isinstance(p, int): return 10 ** 9
    if p[0] == "T": return p[3]
    if p[0] == "G": return min([p[4]] + [min_offset(q) for q in p[1]])
    return min(min_offset(p[1]), min_offset(p[2]))

class Eng:
    def __init__(self):
        self.n0 = 0
        self.ops = []                                  # opcode of every step taken (bookkeeping only)
    def spine(self, a):
        if isinstance(a, int):
            args, h = hc.spine(a); return h, list(args)
        if a[0] == "A":
            h, args = self.spine(a[1]); args.append(a[2]); return h, args
        _, F, X, b = a
        if 1 - b > 60: raise Fail("token unfolded too deep (left comb?)")   # opcodes would depend on n
        self.n0 = max(self.n0, 1 - b)                  # F^(n+b)(X) has a layer to unfold
        T1 = ("T", F, X, b - 1)
        fa, fh = hc.spine(F)
        args = [fill(x, T1) for x in fa]
        if fh == HOLE:
            h2, a2 = self.spine(T1); return h2, a2 + args
        return fh, args
    def step(self, stk):
        if len(stk) < 3: raise Fail("hnf")
        a, b, c = stk[-1], stk[-2], stk[-3]
        if (isinstance(a, int) and a in JUNKSET) or (isinstance(b, int) and b in JUNKSET) or (isinstance(c, int) and c in JUNKSET):
            raise Fail("unknown rest reached")
        if is_seg(a) or is_seg(b) or is_seg(c): raise Fail("pushed segment reached")   # treated like the unknown rest
        h, args = self.spine(a)
        if h != 0: raise Fail("opaque head opened")
        del stk[-3:]
        stk.append(pmk(b, c)); stk.append(c); stk.extend(reversed(args))
        self.ops.append(len(args))
        return len(args)

def window(stk):
    """all items above the unknown rest (patterns and pushed segments)"""
    top = []
    for x in reversed(stk):
        if isinstance(x, int) and x in JUNKSET: break
        top.append(x)
    return top

def det_window(stk):
    """the part above the first pushed segment: what loop detection and block lemmas may use"""
    top = []
    for x in reversed(stk):
        if (isinstance(x, int) and x in JUNKSET) or is_seg(x): break
        top.append(x)
    return top

def with_junk(top):
    return list(JUNKS) + list(reversed(top))

def diff(prev, cur, occ):
    """is cur equal to prev with some comb tokens decremented by one? collects the decremented tokens of cur"""
    if prev == cur: return True
    if is_tok(prev) and is_tok(cur):
        if prev[1:3] == cur[1:3] and cur[3] == prev[3] - 1: occ.append(cur); return True
        return False
    a, b = parts(prev), parts(cur)
    if a is None or b is None or is_tok(prev) or is_tok(cur): return False
    return diff(a[0], b[0], occ) and diff(a[1], b[1], occ)

def abstract(prev, cur, bmin, var=VAR):
    """cur with every decremented token T(F, X, b) replaced by F^(b-bmin)(var)"""
    if prev == cur: return cur
    if is_tok(prev) and is_tok(cur):
        v = var
        for _ in range(cur[3] - bmin): v = fill(cur[1], v)
        return v
    a, b = parts(prev), parts(cur)
    return pmk(abstract(a[0], b[0], bmin, var), abstract(a[1], b[1], bmin, var))

def skel(p):
    if isinstance(p, int): return p
    if p[0] == "T": return ("T", p[1], p[2])
    return ("A", skel(p[1]), skel(p[2]))

def block_lemma(A, F, Lb, opq=OPQ, var=VAR):
    """Lemma LB check: A(F(O)) ->^Lb A(O) on the first len(A) elements, the rest never read. Also returns the block's
    pushes P(V) (the items between A(O) and the unknown rest, with O renamed V): one block maps A(F(T)) ++ r to
    A(T) ++ P(T) ++ r, so m blocks map A(F^m(X)) ++ r to A(X) ++ P(X) ++ P(F X) ++ ... ++ P(F^(m-1) X) ++ r."""
    h = len(A)
    test = [subst(a, fill(F, opq), var) for a in A]; expect = [subst(a, opq, var) for a in A]
    sub = Eng(); s2 = with_junk(test)
    try:
        for _ in range(Lb): sub.step(s2)
    except Fail:
        return False, sub, ()
    res = window(s2)
    if res[:h] != expect: return False, sub, ()
    return True, sub, tuple(repl_atom(q, opq, var) for q in res[h:])

def general_macro(eng, cur, hist, Lmax=170):
    """loop recognised by comparing the window with the one Lb steps earlier"""
    key = tuple(skel(x) for x in cur[:3])
    for Lb in range(1, min(Lmax, len(hist)) + 1):
        prev = hist[-Lb]
        if tuple(skel(x) for x in prev[:3]) != key: continue
        occ = []; h = 0
        while h < min(len(prev), len(cur)):
            o2 = []
            if not diff(prev[h], cur[h], o2): break
            occ += o2; h += 1
        if h < 3 or not occ or len({o[1:3] for o in occ}) != 1: continue
        F, X = occ[0][1], occ[0][2]; bmin = min(o[3] for o in occ)
        for hh in range(h, 2, -1):                      # longest prefix for which the loop lemma holds
            A = [abstract(prev[i], cur[i], bmin) for i in range(hh)]
            if not any(contains(a, VAR) for a in A): break
            ok, sub, P = block_lemma(A, F, Lb)
            if ok:
                eng.n0 = max(eng.n0, sub.n0, -bmin)
                return A, hh, bmin, F, X, Lb, P
    return None

def simple_macro(eng, top, L, opq=OPQ, var=VAR):
    """loop whose variable is exactly one list element p (a token); returns (A, h, b, F, X, L) or None"""
    for p in range(0, min(len(top), 6)):
        e = top[p]
        if not is_tok(e): continue
        _, F, X, b = e
        expect = list(top); expect[p] = opq
        test = list(top); test[p] = fill(F, opq)
        sub = Eng(); s2 = with_junk(test)
        try:
            for _ in range(L): sub.step(s2)
        except Fail:
            continue
        res = window(s2); h = 0
        while h < min(len(res), len(expect)) and res[h] == expect[h]: h += 1
        if h <= p or h < 3: continue
        A = list(top[:h]); A[p] = var
        ok, sub, P = block_lemma(A, F, L, opq, var)
        if not ok: continue
        eng.n0 = max(eng.n0, sub.n0, -b)
        return A, h, b, F, X, L, P
    return None

def prove_cycle(W, L, maxsteps=3000, exact_anchor=None):
    """symbolic cycle lemma; returns (alpha, beta, n0, macros, (a1, be1, M1, ai, R)): M1(n) (the window at anchor ai) is
    reached a1·n + be1 steps after W(n), and M1(n) ->* M1(n+1) takes alpha·n + beta steps.
    exact_anchor=None — the proof pass: below every macro window the rest is unknown (junk), so nothing there is read.
    exact_anchor=i — the residue pass, along the same trajectory: macros keep their pushes as segments and the known items
    below their window, except anchor macro i, below whose pushes the unknown rest B(n) stays; at closure the items between
    the top h1 and the unknown rest form the cycle's residue R(n), so the full list at anchor n+1 is M1(n+1) ++ R(n) ++ B(n)."""
    eng = Eng(); stk = with_junk(W)
    alpha = 0; beta = 0; macros = []; anchors = []; hist = []
    for it in range(maxsteps):
        if eng.n0 > 40: raise Fail("token unfolded too often")
        pre = det_window(stk)
        mac = simple_macro(eng, pre, L) or general_macro(eng, pre, hist)
        if mac is not None:
            A, h, b, F, X, Lb, P = mac                   # state = A(T(F, X, b)); after n+b blocks: A(X), pushes P(...)
            for ai, (A1, h1, b1, F1, X1, a1, be1) in enumerate(anchors):   # does this loop start close a cycle?
                j = b - (b1 + 1)
                if (F, X) == (F1, X1) and h >= h1 and j >= 0 and A[:h1] == [shift(x) for x in A1]:
                    R = None
                    if exact_anchor is not None:
                        full = window(stk)
                        after = [subst(x, ("T", F, X, b - j)) for x in A]
                        pushes = []
                        for i in range(j, 0, -1):         # block i of this loop pushed P(F^(n+b-i) X); the latest on top
                            pushes += [subst(q, ("T", F, X, b - i)) for q in P]
                        R = after[h1:] + pushes + full[h:]
                    return (alpha - a1, beta - be1 + j * Lb, eng.n0, macros,
                            (a1, be1, [subst(x, ("T", F, X, b1)) for x in A1], ai, R))
            anchors.append((A, h, b, F, X, alpha, beta))
            if exact_anchor is None:
                stk = with_junk([subst(x, X) for x in A])
            else:
                below = [] if len(anchors) - 1 == exact_anchor else window(stk)[h:]
                stk = with_junk([subst(x, X) for x in A] + [("G", P, F, X, b)] + below)
            alpha += Lb; beta += b * Lb; macros.append((h, b, Lb)); hist = []
            continue
        hist.append(pre); eng.step(stk); beta += 1
    raise Fail("cycle not closed")

# ---------------------------------------------------------------- concrete side
def opword(ops):
    """the opcode word with ONE character per step (chr(48 + opcode)): '0'..'9' as before, ':' for 10, ';' for 11, …
    — with str() an opcode >= 10 took two characters and every later position drifted from its step number"""
    return "".join(chr(48 + x) for x in ops)

def run(src, N, snap_at=()):
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []; snaps = {}
    want = set(snap_at)
    for n in range(N):
        if n in want: snaps[n] = stk[::-1][:40]
        if len(stk) < 3: return None, snaps
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(len(ch))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
        if len(hc.L) > 6_000_000: return None, snaps
    return ops, snaps

def tokens(w, B):
    i = 0; out = []
    while i < len(w):
        if w.startswith(B, i):
            s = i; k = 0
            while w.startswith(B, i): i += len(B); k += 1
            out.append(("B", s, k))
        else:
            j = i
            while j < len(w) and not w.startswith(B, j): j += 1
            out.append(("D", i, w[i:j])); i = j
    return out

def find_cycles(w):
    """block word B and the cycle starts (start of one loop per cycle, with its count n)"""
    """all candidate cycle structures (B, q, starts), shortest block first (then fewest tokens)"""
    scores = sorted(((sum(w[i] == w[i - p] for i in range(p, len(w))) / len(w), p) for p in range(1, 40)), reverse=True)
    results = []
    for p in sorted({p for sc, p in scores[:4]}):        # several candidate block lengths, not only the best one
        results += sorted(_cycles_for_period(w, p))
    if not results:                                       # long blocks (up to 160 steps) only if no short one works
        ws = w[:30000]
        long_scores = sorted(((sum(ws[i] == ws[i - p] for i in range(p, len(ws))) / len(ws), p) for p in range(40, 161)),
                             reverse=True)
        for p in sorted({p for sc, p in long_scores[:4]}):
            results += sorted(_cycles_for_period(w, p))
    return [r[1:] for r in results]

def find_cycles_marker(w, maxq=12):
    """cycle starts from a marker symbol instead of a repeated block — for cycles whose loops have different blocks (the
    separators between runs of one block then contain the other loops and are never equal, so find_cycles sees nothing).
    A symbol occurring q times per cycle: in the tail of the run, for every phase the q-strided gaps must grow by the same
    d >= 1 per cycle (cycle length affine in n). Returns candidates (marker, q, starts) with starts = every q-th occurrence
    (one phase), counted n = 10, 11, … (any consistent count works: patterns are written relative to the first start)."""
    out = []
    counts = collections.Counter(w)
    for c, k in sorted(counts.items(), key=lambda x: x[1]):
        if k < 40 or k > len(w) // 10: continue
        pos = [i for i, x in enumerate(w) if x == c]
        tail = pos[len(pos) // 3:]
        for q in range(1, maxq + 1):
            if len(tail) < 8 * q: break
            g = [tail[i + q] - tail[i] for i in range(len(tail) - q)]
            dd = {g[i + q] - g[i] for i in range(len(g) - q)}
            if len(dd) == 1 and next(iter(dd)) >= 1:
                for ph in range(q):
                    starts = [(tail[i], 10 + j) for j, i in enumerate(range(ph, len(tail), q))]
                    out.append((c, q, starts))
                break
    return out

def _cycles_for_period(w, p):
    B0 = collections.Counter(w[i:i + p] for i in range(len(w) // 2, len(w) - p)).most_common(1)[0][0]
    results = []
    for r in range(p):
        B = B0[r:] + B0[:r]
        toks = tokens(w, B)
        ph = []
        for i, t in enumerate(toks[:-2]):                 # the word is cut off at N steps: ignore the last, partial phase
            if t[0] == "B" and toks[i + 1][0] == "D": ph.append((t[1], t[2], toks[i + 1][2]))
        if len(ph) < 12: continue
        tail = ph[len(ph) // 3:]
        for q in range(1, 25):
            if len(tail) < 3 * q + 3: break
            ok = all(tail[j + q][2] == tail[j][2] and tail[j + q][1] - tail[j][1] in (0, 1) for j in range(len(tail) - q))
            inc = [tail[j + q][1] - tail[j][1] for j in range(q)]
            if ok and 1 in inc:
                j0 = inc.index(1)
                starts = [(tail[j][0], tail[j][1]) for j in range(j0, len(tail), q)]
                results.append((len(toks), B, q, starts))
                break
    return results

def holeify(t, s, memo):
    """t with every occurrence of s replaced by HOLE"""
    if t == s: return HOLE
    if t <= 0: return t
    if t in memo: return memo[t]
    r = hc.app(holeify(hc.L[t], s, memo), holeify(hc.R[t], s, memo)); memo[t] = r; return r

CTX_LIMIT = 5000                                       # largest comb context accepted from holeify (tree size)

def family_lookup(fams, n_hi):
    """{(F^k(X), F^(k+1)(X)): (F, X, k)} for the known comb families, k <= n_hi + 2"""
    look = {}
    for F, X in fams:
        c = X
        for k in range(n_hi + 3):
            nxt = fill(F, c); look.setdefault((c, nxt), (F, X, k)); c = nxt
    return look

def anti(t1, t2, n1, memo, look=None):
    """pattern W with W(n1) = t1 and W(n1+1) = t2: subterm pairs that are consecutive members of a known comb family
    become its tokens; otherwise t2 = F(t1) with a small context F gives a new family; otherwise recurse"""
    key = (t1, t2)
    if key in memo: return memo[key]
    if t1 == t2: r = t1
    elif look is not None and key in look:
        F, X, k = look[key]; r = ("T", F, X, k - n1)
    else:
        F = holeify(t2, t1, {}) if t1 > 0 and t2 > 0 and hc.size(t1) < hc.size(t2) else t2
        if F != t2 and F != HOLE and hc.size(F) <= CTX_LIMIT:
            a = 0; X = t1
            while True:
                v = match(F, X, MISSING)
                if v is FAIL or v is MISSING or not isinstance(v, int): break
                X = v; a += 1
            FAMILIES.add((F, X))
            r = ("T", F, X, a - n1)
        elif t1 > 0 and t2 > 0:
            r = pmk(anti(hc.L[t1], hc.L[t2], n1, memo, look), anti(hc.R[t1], hc.R[t2], n1, memo, look))
        else:
            raise Fail("no comb pattern")
    memo[key] = r; return r

def anti_window(st1, st2, n1, wlen):
    """two passes: (1) find comb families element by element; (2) re-anti-unify every element with the family lookup,
    so elements built from other elements' combs (coupled recurrences) are expressed with their tokens"""
    fams = set()
    for j in range(wlen):
        try:
            for tk in toks_in(anti(st1[j], st2[j], n1, {})): fams.add((tk[1], tk[2]))
        except Fail:
            pass
    look = family_lookup(fams, n1)
    memo = {}
    return [anti(st1[j], st2[j], n1, memo, look) for j in range(wlen)]

def prove(src, N=60000):
    ops, _ = run(src, N)
    if ops is None: return {"status": "run failed"}
    w = opword(ops)
    cands = find_cycles(w)
    first_fail = None
    for B, q, starts in cands:                           # shortest block first; the first certificate found is returned
        r = prove_with(src, B, q, starts)
        if r["status"] == "PROVED": return r
        if first_fail is None: first_fail = r
    # cycles whose loops have different blocks: cycle starts from a marker symbol (tried only if the above found nothing)
    for c, q, starts in find_cycles_marker(w)[:12]:
        r = prove_with(src, c, q, starts)
        if r["status"] == "PROVED": return r
        if first_fail is None: first_fail = r
    return first_fail or {"status": "no growing loop cycle"}

def prove_with(src, B, q, starts):
    L = len(B)
    if len(starts) < 5: return {"status": "too few cycles", "B": B}
    pos = [s for s, k in starts]
    _, snaps = run(src, pos[-1] + 1, snap_at=pos)
    last = {"status": "no pattern", "B": B, "q": q}
    tried = 0
    for i0 in range(1, len(starts) - 3):
        (s1, n1), (s2, n2), (s3, n3) = starts[i0], starts[i0 + 1], starts[i0 + 2]
        if n2 != n1 + 1 or n3 != n2 + 1: continue
        tried += 1
        if tried > 3: break
        for wlen in range(3, 11):
            st1, st2, st3 = snaps[s1], snaps[s2], snaps[s3]
            if min(len(st1), len(st2), len(st3)) < wlen: break
            try:
                W = anti_window(st1, st2, n1, wlen)
                if any(inst(W[j], n3) != st3[j] for j in range(wlen)): continue
                alpha, beta, n0, macros, delta = prove_cycle(W, L)
                n0 = max([n0] + [-min_offset(x) for x in W + delta[2]])   # every token count n + b >= 0
            except Fail as e:
                last = {"status": f"cycle lemma fails ({e})", "B": B, "q": q}
                continue
            # transient: the first cycle start with n >= n0 is an instance of W
            first = next(((s, n) for s, n in starts if n >= max(n0, 0)), None)
            if first is None: return {"status": "no cycle start with n >= n0", "B": B}
            st = snaps[first[0]]
            if any(inst(W[j], first[1]) != st[j] for j in range(wlen)):
                last = {"status": "transient instance fails", "B": B}; continue
            # cross-check (numerical, independent of the proof): for every later cycle start (s, n) the concrete state at
            # time s + a1·n + be1 is an instance of M(n), and alpha·n + beta steps later an instance of M(n+1)
            a1, be1, M1, ai, _ = delta
            later = [(s, n) for s, n in starts if s >= first[0]]
            times = {}
            for s, n in later:
                t = s + a1 * n + be1; times[t] = n; times[t + alpha * n + beta] = n + 1
            _, cs = run(src, max(times) + 1, snap_at=list(times))
            ok = [all(inst(M1[j], times[t]) == cs[t][j] for j in range(len(M1))) for t in sorted(times) if t in cs]
            fams = {(tk[1], tk[2]) for x in W + M1 for tk in toks_in(x)}
            nonlinear = sum(1 for F, X in fams if hc.R[F] != HOLE or contains(hc.L[F], HOLE))
            kwin = residue_check(W, L, ai, alpha, beta, M1, later, a1, be1, cs)
            return {"status": "PROVED", "B": B, "q": q, "window": wlen, "alpha": alpha, "beta": beta, "n0": n0,
                    "macros": len(macros), "first_cycle": first, "crosscheck": (sum(ok), len(times)), "contexts": nonlinear,
                    "kwin": kwin}
    return last

def residue_check(W, L, ai, alpha, beta, M1, later, a1, be1, cs, K=30):
    """residue pass + numerical test of the full-list description: at the anchor of cycle n the list is
    M1(n) ++ R(n-1) ++ R(n-2) ++ ... ++ R(n_s) ++ B(n_s) (B(n_s) = the concrete list below M1 at the base anchor n_s);
    compares the first K entries with the concrete run at every later anchor. Returns (passed, total, |R|) or None."""
    try:
        r2 = prove_cycle(W, L, exact_anchor=ai)
    except Fail:
        return None
    R = r2[4][4]
    # the residue pass must replay the proof's trajectory: same cycle length AND the same closing anchor
    if R is None or (r2[0], r2[1]) != (alpha, beta) or r2[4][3] != ai: return None
    need = max([0] + [-min_offset(x) for x in R])                  # R(m) denotes a list only for m >= need
    at = [(n, s + a1 * n + be1) for s, n in later]
    base = next(((n, t) for n, t in at if n >= need and t in cs), None)
    if base is None: return None
    ns, ts = base; h1 = len(M1); Bs = cs[ts][h1:]
    passed = total = 0
    for n, t in at:
        if n <= ns or t not in cs: continue
        pred = [inst(x, n) for x in M1]
        for m in range(n - 1, ns - 1, -1):
            if len(pred) >= K: break
            pred += expand(R, m, K - len(pred))
        pred += Bs
        k = min(K, len(cs[t]), len(pred))
        total += 1; passed += pred[:k] == cs[t][:k]
    return passed, total, len(R)

def toks_in(p):
    if isinstance(p, int): return []
    if p[0] == "T": return [p]
    if p[0] == "G": return [tk for q in p[1] for tk in toks_in(q)]
    return toks_in(p[1]) + toks_in(p[2])

if __name__ == "__main__":
    for src in sys.argv[1:]:
        r = prove(src)
        extra = ""
        if r["status"] == "PROVED":
            extra = (f"  (B = {r['B']}, {r['q']} loop(s) per cycle, window {r['window']}, cycle length {r['alpha']}·n + {r['beta']},"
                     f" n >= {r['n0']}, {r['macros']} macro(s), first cycle {r['first_cycle']}, cross-check {r['crosscheck'][0]}/{r['crosscheck'][1]}"
                     + (f", {r['contexts']} non-linear comb famil{'y' if r['contexts'] == 1 else 'ies'}" if r['contexts'] else "") + ")")
        print(f"{src}: {r['status']}{extra}", flush=True)
        if r["status"] == "PROVED":
            kw = r.get("kwin")
            print("    whole list (every window size): " + (f"residue of {kw[2]} items per cycle; first 30 entries checked at "
                  f"{kw[0]}/{kw[1]} anchors" if kw else "not determined"), flush=True)
