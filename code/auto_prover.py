"""Automatic exact-structure prover for counter head runs (main agent, 2026-10-26).

Pipeline for a term t:
 1. level family: frequent front elements whose generic behaviour (run of [P, x, y, r..] until an atom-headed front) has
    the same return top three and geometrically growing time (level_finder);
 2. scheme: one-or-more-hole context F with L_{k+1} = F[L_k] (holes = occurrences of L_k), checked on three members;
 3. return form R(Z): the generic return top three, which must be a function of Z = x·y only;
 4. symbolic engine with level tokens L(d) (unfold L(d) = F[L(d-1)], fold F[L(e)] -> L(e+1)) and two macros:
      CALL   [L(d), a, b | ?] -> R(a·b) + ?                       (call lemma, level j+d)
      RESUME top three = the state of a level-(d+1) call just before its first inner call, with product Z -> R(Z) + ?
    (the resume pattern is computed symbolically from [L(1), x, y]);
 5. call lemma inductive step for all j >= JMIN with macros only below level j; base levels checked concretely;
 6. driver: event configurations R(Z_k) found in the concrete run, Z_k = G[L_k] for a context G; symbolic derivation
    R(G[L(0)]) -> R(G[L(1)]); transient checked concretely.
Everything symbolic is valid for all levels >= JMIN; the concrete checks cover the finitely many remaining cases.
"""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse, show
import hc

JUNK = "?"
H = "HOLE"

# ---------- concrete helpers (hash-consed) ----------
def generic_return(P, cap=30000):
    """run [P, x, y, r1..r4]; return (time, top three) at the first atom-headed front, else None"""
    stk = [-6, -5, -4, -3, -2, -1, P]
    for t in range(cap):
        a = stk[-1]; ch, h = hc.spine(a)
        if h != 0: return t, stk[-1:-4:-1]
        if len(stk) < 4: return None
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return None

def to_tuple(i, sub=None):
    """hash-consed id -> tuple term; sub maps ids to replacement objects (e.g. holes/tokens)"""
    if sub and i in sub: return sub[i]
    if i == 0: return "S"
    if i == -1: return "x"
    if i == -2: return "y"
    if i < 0: return f"r{-i - 2}"
    return (to_tuple(hc.L[i], sub), to_tuple(hc.R[i], sub))

def contains(i, j):
    if i == j: return True
    if i <= 0: return False
    return contains(hc.L[i], j) or contains(hc.R[i], j)

def subst_hole(F, X):
    if F == H: return X
    if isinstance(F, tuple): return (subst_hole(F[0], X), subst_hole(F[1], X))
    return F

def from_tuple(t):
    if t == "S": return 0
    if t == "x": return -1
    if t == "y": return -2
    return hc.app(from_tuple(t[0]), from_tuple(t[1]))

# ---------- step 1-3: levels, scheme, return form ----------
def find_family(src, steps=30000, top=200):
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; freq = collections.Counter()
    for n in range(steps):
        if len(stk) < 3: break
        a = stk[-1]; freq[a] += 1
        stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    XY = hc.app(-1, -2)
    groups = collections.defaultdict(list)
    for a, f in freq.most_common(top):
        if hc.size(a) < 4: continue
        g = generic_return(a)
        if g is None: continue
        T, top3 = g
        key = tuple(top3)
        groups[key].append((hc.size(a), T, a))
    fams = []
    for key, mem in groups.items():
        mem = sorted(set(mem))
        if len(mem) >= 3:
            # levels must nest: each member contains the previous one and has a larger call time. A group can also hold
            # other fronts with the same return form, so take the longest such chain (longest path, by size order).
            n_ = len(mem); ln = [1] * n_; prev = [-1] * n_
            for i in range(n_):
                for j in range(i):
                    if mem[i][1] > mem[j][1] and ln[j] + 1 > ln[i] and contains(mem[i][2], mem[j][2]):
                        ln[i] = ln[j] + 1; prev[i] = j
            i = max(range(n_), key=lambda k: ln[k]); best = []
            while i >= 0: best.append(mem[i]); i = prev[i]
            best.reverse()
            greedy = [mem[0]]                            # the original rule: greedy chain from the smallest member
            for m in mem[1:]:
                if contains(m[2], greedy[-1][2]) and m[1] > greedy[-1][1]: greedy.append(m)
            for ch_ in ([greedy] if greedy != best else []) + [best]:
                if len(ch_) >= 3 and ch_[-1][1] > 12: fams.append((key, ch_))
    return fams

def infer_scheme(chain):
    """context F (holes for L_k) with L_{k+1} = F[L_k], verified on the chain"""
    for i in range(len(chain) - 2):
        Lk, Lk1 = chain[i][2], chain[i + 1][2]
        F = to_tuple(Lk1, {Lk: H})
        ok = all(from_tuple_with(F, chain[j][2]) == chain[j + 1][2] for j in range(i, len(chain) - 1))
        if ok: return F, i
    return None, None

def infer_scheme_trim(chain):
    """infer_scheme on the whole chain, else on the chain without trailing members (a last member observed near the end of
    the sampled run can be misdetected); at least three members from the scheme base on must fit. Returns (F, i0, chain).
    Dropping members only removes base-case material: every level is defined by the scheme itself, and the call lemma,
    driver derivation and strong checks below do not depend on the dropped members."""
    for end in range(len(chain), 2, -1):
        F, i0 = infer_scheme(chain[:end])
        if F is not None and end - i0 >= 3: return F, i0, chain[:end]
    return None, None, chain

def from_tuple_with(F, X):
    if F == H: return X
    if F == "S": return 0
    return hc.app(from_tuple_with(F[0], X), from_tuple_with(F[1], X))

def return_form(top3):
    """express the return top three as functions of Z = x·y; None if x or y occur outside Z"""
    XY = hc.app(-1, -2)
    out = []
    for e in top3:
        t = to_tuple(e, {XY: "Z", -1: "X", -2: "Y"})
        if "r" in str(t): return None          # tape atoms must not appear
        out.append(t)
    return out

def _has_atom(t):
    if t in ("x", "y"): return True
    if isinstance(t, tuple): return _has_atom(t[0]) or _has_atom(t[1])
    return False

# ---------- step 4: symbolic engine ----------
class Scheme:
    def __init__(self, F, R):
        self.F, self.R = F, R
    def L(self, d): return ("L", d)
    def is_tok(self, t): return isinstance(t, tuple) and len(t) == 2 and t[0] == "L" and isinstance(t[1], int)
    def body(self, d):
        """F[L(d-1)] (tokens inside)"""
        return self.inst(self.F, ("L", d - 1))
    def inst(self, F, X):
        if F == H: return X
        if F == "S": return "S"
        return (self.inst(F[0], X), self.inst(F[1], X))
    def toks(self, t, acc):
        if self.is_tok(t): acc.add(t[1]); return
        if isinstance(t, tuple): self.toks(t[0], acc); self.toks(t[1], acc)
    def mk(self, f, a):
        t = (f, a)
        acc = set(); self.toks(t, acc)
        for e in acc:
            if t == self.inst(self.F, ("L", e)): return ("L", e + 1)
        return t
    def halves(self, Z):
        if self.is_tok(Z): Z = ("S", self.body(Z[1]))
        if not isinstance(Z, tuple): raise ValueError("product is not an application")
        return Z[0], Z[1]
    def R_of(self, Z):
        y_only = ("Z" not in str(self.R)) and ("X" not in str(self.R))
        if y_only and isinstance(Z, tuple) and len(Z) == 2 and Z[0] == "YONLY": X, Y = None, Z[1]
        else: X, Y = self.halves(Z) if ("X" in str(self.R) or "Y" in str(self.R)) else (None, None)
        def ev(t):
            if t == "Z": return Z
            if t == "X": return X
            if t == "Y": return Y
            if t == "S": return "S"
            return self.mk(ev(t[0]), ev(t[1]))
        return [ev(t) for t in self.R]
    def spine(self, t):
        a = []
        while isinstance(t, tuple) and not self.is_tok(t): a.append(t[1]); t = t[0]
        a.reverse(); return t, a

class Engine:
    def __init__(self, sch, jmin, maxlev=10 ** 9, resume=None):
        self.s, self.jmin, self.maxlev, self.items, self.resume = sch, jmin, maxlev, [], resume
    def open_front(self, e):
        h, args = self.s.spine(e)
        if h == "S": return args
        if self.s.is_tok(h):
            if self.jmin + h[1] < 1: raise ValueError("level may be 0")
            bh, bargs = self.s.spine(self.s.body(h[1]))
            if bh != "S": raise ValueError("level body not S-headed")
            return bargs + args
        raise ValueError(f"opaque element opened: {h}")
    def match_resume(self, K):
        """resume pattern: list of three templates over L(0) (as 'L', 0 relative) and 'Z'; returns (d, Z) or None"""
        if self.resume is None or not self.s.is_tok(K[0]): return None
        d = K[0][1]
        pat = self.resume
        def shift(t, dd):
            if self.s.is_tok(t): return ("L", t[1] + dd)
            if isinstance(t, tuple): return (shift(t[0], dd), shift(t[1], dd))
            return t
        Z = None
        def match(p, t):
            nonlocal Z
            if p == "Z":
                if Z is None: Z = t; return True
                return Z == t
            if isinstance(p, tuple) and not (len(p) == 2 and p[0] == "L" and isinstance(p[1], int)):
                return isinstance(t, tuple) and not self.s.is_tok(t) and match(p[0], t[0]) and match(p[1], t[1])
            return p == t
        sp = [shift(p, d) for p in pat]
        if all(match(p, t) for p, t in zip(sp, K[:3])) and Z is not None: return d, Z
        return None
    def run(self, K, goal, cap=4000):
        for n in range(cap):
            if K[:3] == goal[:3]: return n
            if JUNK in K[:3]: raise ValueError("unknown rest reached the top three")
            m = self.match_resume(K)
            if m and m[0] + 1 <= self.maxlev and self.jmin + m[0] + 1 >= 1:
                self.items.append(("resume", m[0] + 1)); K = self.s.R_of(m[1]) + [JUNK]; continue
            if self.s.is_tok(K[0]) and K[0][1] <= self.maxlev:
                d = K[0][1]
                if self.jmin + d < 0: raise ValueError("call at negative level")
                self.items.append(("call", d)); K = self.s.R_of(self.s.mk(K[1], K[2])) + [JUNK]; continue
            ch = self.open_front(K[0]); self.items.append(("eng", len(ch)))
            K = ch + [K[2], self.s.mk(K[1], K[2])] + K[3:]
        return None

RESUME_STEPS = [None]
def concrete_remainder_barrier(levels, k, R, cap=2_000_000):
    """base-level check of RESUME: in the concrete generic call of level k+1 ([L_{k+1}, x, y | tape]), at the resume
    point (first time L_k is the front) replace everything below the top three by fresh atoms; the remainder must
    return R(x·y) without any fresh atom reaching the top three (so it never reads below the resume state's top three)"""
    P, inner = levels[k + 1], levels[k]
    stk = [-6, -5, -4, -3, -2, -1, P]; fresh = None
    for t in range(cap):
        a = stk[-1]
        if t > 0 and a == inner and fresh is None:
            below = len(stk) - 3; fresh = [-100 - i for i in range(below)]; stk[:below] = fresh
        if fresh is not None and any(x in fresh for x in stk[-3:]): return False
        ch, h = hc.spine(a)
        if h != 0: break
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    else:
        return False
    return fresh is not None and tuple(stk[-1:-4:-1]) == R_concrete(R, hc.app(-1, -2))

def resume_pattern(sch, jmin=3, levels=None, i0=None):
    """run [L(1), x, y] symbolically until the front is a bare token L(0) with two arguments: that top three, with x·y
    renamed Z and tokens relative to level 0, is the resume pattern"""
    E = Engine(sch, jmin, maxlev=-10)
    K = [("L", 1), "x", "y", JUNK]
    for n in range(200):
        if sch.is_tok(K[0]) and K[0][1] == 0 and n > 0:
            def rn(t):
                if t == ("x", "y"): return "Z"
                if isinstance(t, tuple) and not sch.is_tok(t): return (rn(t[0]), rn(t[1]))
                return t
            top = [rn(t) for t in K[:3]]
            if _has_atom(top): return None
            RESUME_STEPS[0] = n
            # soundness of RESUME (main agent, 2026-10-26, later): the barrier criterion — the remainder, run from the
            # resume state's top three with the unknown rest directly below (inner call by CALL, resumes only at strictly
            # lower levels), returns R(x·y) without reading below its top three; then RESUME is sound whatever lies
            # below. Symbolic for inner levels >= jr; the inner levels 0..jr-1 (relative to the family base) are checked
            # concretely with fresh atoms below the resume state's top three. (An earlier version accepted the head test
            # alone — every element below the top three headed by an argument — which is not sufficient: the generic
            # call's return event could itself be the opening of such an element, and RESUME would then depend on what
            # lies below. It is no longer used.)
            if levels is None: return "UNSAFE"
            jr = None
            for j_ in range(1, 6):
                E1 = Engine(sch, j_, maxlev=0, resume=top)
                try:
                    if E1.run(K[:3] + [JUNK], sch.R_of(("x", "y"))) is not None: jr = j_; break
                except ValueError:
                    continue
            if jr is None: return "UNSAFE"
            for k in range(jr):
                while len(levels) <= i0 + k + 1: levels.append(from_tuple_with(sch.F, levels[-1]))
                if not concrete_remainder_barrier(levels, i0 + k, sch.R): return "UNSAFE"
            return top
        ch = E.open_front(K[0])
        K = ch + [K[2], sch.mk(K[1], K[2])] + K[3:]
    return None


def shift_tok(t, dd):
    if isinstance(t, tuple) and len(t) == 2 and t[0] == "L" and isinstance(t[1], int): return ("L", t[1] + dd)
    if isinstance(t, tuple): return (shift_tok(t[0], dd), shift_tok(t[1], dd))
    return t

def first_appearance_templates(src, levels, steps=40000):
    """{k: (template of the top three relative to level k, step)} at the first time level k is the bare front element"""
    lev = {L: k for k, L in enumerate(levels)}
    def rel(i, k):
        if i in lev: return ("L", lev[i] - k)
        if i == 0: return "S"
        if i < 0: return f"atom{i}"
        return (rel(hc.L[i], k), rel(hc.R[i], k))
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; out = {}
    for n in range(steps):
        if len(stk) < 3: break
        a = stk[-1]
        if a in lev and lev[a] not in out:
            k = lev[a]; out[k] = (tuple(rel(e, k) for e in stk[-1:-4:-1]), n)
        stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return out

def trace(items): return " ".join(str(v) if k == "eng" else f"[{k} {v:+d}]" for k, v in items)

# ---------- driver discovery ----------
def find_events(src, chain, R, steps=60000):
    """moments where the top three equal R(Z) for some Z; return [(step, Z)]"""
    y_only = ("Z" not in str(R)) and ("X" not in str(R))
    def R_conc(Z):
        if y_only:
            X, Y = None, Z
        elif Z <= 0: return None
        else: X, Y = hc.L[Z], hc.R[Z]
        def ev(t):
            if t == "Z": return Z
            if t == "X": return X
            if t == "Y": return Y
            if t == "S": return 0
            return hc.app(ev(t[0]), ev(t[1]))
        return [ev(t) for t in R]
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]
    def candidates(e):
        out = [e]
        if e > 0: out += [hc.L[e], hc.R[e]]
        if e > 0 and hc.L[e] > 0: out += [hc.L[hc.L[e]], hc.R[hc.L[e]]]
        return out
    for n in range(steps):
        if len(stk) < 3: break
        top = stk[-1:-4:-1]
        for Z in candidates(top[0]):
            if Z > 0 and R_conc(Z) == top: yield (n, Z); break
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))


def R_concrete(R, Z):
    """the concrete top three R(Z) (as in find_events)"""
    y_only = ("Z" not in str(R)) and ("X" not in str(R))
    if y_only: X, Y = None, Z
    elif Z <= 0: return None
    else: X, Y = hc.L[Z], hc.R[Z]
    def ev(t):
        if t == "Z": return Z
        if t == "X": return X
        if t == "Y": return Y
        if t == "S": return 0
        return hc.app(ev(t[0]), ev(t[1]))
    return tuple(ev(t) for t in R)

def strong_check(src, chain, F, i0, step_j, step_items, drv_j, drv_items, G=None, R=None, T0=None, k_from=0,
                 N=400000, KMAX=60):
    """independent numerical test of a call-prover proof (main agent, 2026-10-26): (1) the derived call-step recursion
    reproduces every concrete call time of the chain it applies to; (2) levels beyond the chain are built with the scheme
    (L_{k+1} = F[L_k]) and their call times with the recursion, and every observed gap between consecutive driver events
    (events R(G[L_k]), or first appearances of L_k as front element with top-three template T0) in the first N steps of
    the concrete run equals the cost of the derived driver trace. Returns (passed, total)."""
    sres = RESUME_STEPS[0]
    levels = [m[2] for m in chain]
    T = {kk: chain[kk][1] for kk in range(len(chain))}
    def cost(kk, items):
        c = 0
        for kind, v in items:
            if kind == "eng": c += 1
            elif kind == "call": c += T[kk + v]
            else: c += T[kk + v] - sres
        return c
    checks = []
    for kk in range(len(chain)):
        if kk - i0 >= step_j and all(kk + v in T for kind, v in step_items if kind != "eng"):
            checks.append(cost(kk, step_items) == T[kk])
    while len(levels) < KMAX:
        kk = len(levels); levels.append(from_tuple_with(F, levels[-1])); T[kk] = cost(kk, step_items)
        if T[kk] > 10 ** 8: break
    seen = {}
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]
    if T0 is None:
        expected = {}
        for kk in range(len(levels)):
            top = R_concrete(R, from_tuple_with(G, levels[kk]))
            if top is not None: expected.setdefault(top, kk)
        for n in range(N):
            if len(stk) < 3: break
            k = expected.get((stk[-1], stk[-2], stk[-3]))
            if k is not None and k not in seen: seen[k] = n
            a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    else:
        lev = {L: kk for kk, L in enumerate(levels)}
        def rel(i, k):
            if i in lev: return ("L", lev[i] - k)
            if i == 0: return "S"
            if i < 0: return f"atom{i}"
            return (rel(hc.L[i], k), rel(hc.R[i], k))
        for n in range(N):
            if len(stk) < 3: break
            a = stk[-1]
            if a in lev and lev[a] not in seen and tuple(rel(e, lev[a]) for e in stk[-1:-4:-1]) == T0: seen[lev[a]] = n
            stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    for kk in sorted(seen):
        if kk + 1 in seen and kk >= k_from and kk - i0 >= drv_j and all(kk + v in T for kind, v in drv_items if kind != "eng"):
            checks.append(seen[kk + 1] - seen[kk] == cost(kk, drv_items))
    return sum(checks), len(checks)

def prove(src, verbose=True):
    fams = find_family(src)
    report = {"term": src, "status": "no level family"}
    for key, chain in fams:
        F, i0, chain = infer_scheme_trim(chain)
        if F is None: report["status"] = "no scheme"; continue
        R = return_form(key)
        if R is None: report["status"] = "return form not a function of x·y"; continue
        sch = Scheme(F, R)
        try: res = resume_pattern(sch, levels=[m[2] for m in chain], i0=i0)
        except ValueError: report["status"] = "resume pattern not computable"; continue
        if res == "UNSAFE": res = None          # RESUME is available only when its barrier holds; derive without it
        # call step
        step_ok = None
        for jmin in range(1, 6):
            E = Engine(sch, jmin, maxlev=-1, resume=res)
            K = [("L", 0), "x", "y", JUNK]
            try:
                first = E.open_front(K[0]); E.items.append(("eng", len(first)))
                K = first + [K[2], sch.mk(K[1], K[2])] + K[3:]
                n = E.run(K, sch.R_of(("x", "y")))
            except ValueError: continue
            if n is not None: step_ok = (jmin, trace(E.items)); step_items = list(E.items); break
        if step_ok is None: report["status"] = "call step not derived"; continue
        # rigour: the inductive step holds for levels >= jmin (relative to the chain base chain[i0]); the levels below
        # are base cases, which must be consecutive scheme levels satisfying the call lemma concretely (they are chain
        # members, grouped by their concrete generic return) — require at least jmin + 1 of them from i0 on
        if len(chain) - i0 < step_ok[0] + 1:
            report.update(status="too few concrete base levels", step=step_ok); continue
        # base levels: the chain's smallest member and unfoldings must return R concretely for levels < jmin
        base = chain[i0][2]
        # driver: events R(Z_k); Z_k = G[L_k]
        levels = [m[2] for m in chain]
        lev_index = {L: k for k, L in enumerate(levels)}
        memo_ml = {}
        def maxlev(i):
            if i in lev_index: return lev_index[i]
            if i <= 0: return -1
            r = memo_ml.get(i)
            if r is None:
                r = max(maxlev(hc.L[i]), maxlev(hc.R[i])); memo_ml[i] = r
            return r
        bykey = collections.defaultdict(dict); drv = None
        for n1, Z1 in find_events(src, chain, R, steps=60000):
            kmax = maxlev(Z1)
            if kmax < 0: continue
            G = to_tuple(Z1, {levels[kmax]: H})
            if H not in str(G): continue
            ks = bykey[G]; ks.setdefault(kmax, n1)
            if kmax - 1 in ks and kmax - 2 in ks:
                drv = (G, ks[kmax], kmax); break
        def template_driver():
            """fallback: template driver — top three at the first appearance of each level at the front, written with
            level tokens relative to that level; a template repeating at consecutive levels is derived symbolically"""
            tpl = first_appearance_templates(src, levels)
            for kk in sorted(tpl):
                if kk + 1 in tpl and kk + 2 in tpl and tpl[kk][0] == tpl[kk + 1][0] == tpl[kk + 2][0]:
                    T0 = tpl[kk][0]
                    for jmin in range(1, 6):
                        E = Engine(sch, jmin, resume=res)
                        try:
                            n = E.run([shift_tok(t, 0) for t in T0] + [JUNK], [shift_tok(t, 1) for t in T0])
                        except ValueError: continue
                        if n is not None:
                            if kk - i0 < jmin: break
                            # independent numerical test: call-time recursion and first-appearance gaps (strong_check)
                            ok = strong_check(src, chain, F, i0, step_ok[0], step_items, jmin, list(E.items), T0=T0, k_from=kk)
                            return (jmin, trace(E.items), tpl[kk][1], kk, ok, T0)
            return None
        def template_report(done):
            report.update(status="PROVED", step=step_ok, driver=(done[0], done[1]), event_step=done[2], scheme=F,
                          base_size=hc.size(base), event_level=done[3] - i0, crosscheck=done[4],
                          _int=dict(chain=chain, F=F, i0=i0, R=R, res=res, step_j=step_ok[0], drv_kind="template", T0=done[5],
                                    drv_j=done[0], kk=done[3]))
            return report
        if drv is None:
            done = template_driver()
            if done is None:
                report.update(status="call step derived; driver configuration not found", step=step_ok); continue
            return template_report(done)
        G, n1, k = drv
        dr_ok = None
        for jmin in range(1, 6):
            E = Engine(sch, jmin, resume=res)
            try:
                y_only = ("Z" not in str(R)) and ("X" not in str(R))
                w0, w1 = sch.inst(G, ("L", 0)), sch.inst(G, ("L", 1))
                if y_only: w0, w1 = ("YONLY", w0), ("YONLY", w1)
                n = E.run(sch.R_of(w0) + [JUNK], sch.R_of(w1))
            except ValueError: continue
            if n is not None: dr_ok = (jmin, trace(E.items)); break
        if dr_ok is None:
            done = template_driver()                 # the event driver failed: try the template driver as well
            if done is None: report.update(status="call step derived; driver not derived", step=step_ok); continue
            return template_report(done)
        if k - i0 < dr_ok[0]:
            report.update(status="driver event below the driver's minimum level", step=step_ok, driver=dr_ok); continue
        # independent numerical test: call-time recursion and driver-event gaps over a long run (strong_check)
        E2 = Engine(sch, dr_ok[0], resume=res)
        w0, w1 = sch.inst(G, ("L", 0)), sch.inst(G, ("L", 1))
        if ("Z" not in str(R)) and ("X" not in str(R)): w0, w1 = ("YONLY", w0), ("YONLY", w1)
        E2.run(sch.R_of(w0) + [JUNK], sch.R_of(w1))
        report.update(status="PROVED", step=step_ok, driver=dr_ok, event_step=n1, scheme=F, base_size=hc.size(base),
                      event_level=k - i0, crosscheck=strong_check(src, chain, F, i0, step_ok[0], step_items, dr_ok[0],
                                                                   list(E2.items), G=G, R=R),
                      _int=dict(chain=chain, F=F, i0=i0, R=R, res=res, step_j=step_ok[0], drv_kind="events", G=G,
                                drv_j=dr_ok[0], kk=k))
        return report
    return report

if __name__ == "__main__":
    for src in sys.argv[1:]:
        r = prove(src)
        print(f"{src}: {r['status']}")
        if "step" in r: print(f"    call step (j >= {r['step'][0]}): {r['step'][1]}")
        if "driver" in r: print(f"    driver (k >= {r['driver'][0]}): {r['driver'][1]}; first event at step {r['event_step']}")
        if "crosscheck" in r: print(f"    event-time cross-check: {r['crosscheck'][0]}/{r['crosscheck'][1]} (call-time recursion on the "
                                    f"concrete levels + driver-event gaps in the first 400,000 steps)")
