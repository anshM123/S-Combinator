"""Parallel loop prover (main agent, 2026-10-26): Theorem LP's method for parallel (ReplaceAll) evolution.
The loop prover (code/loop_prover.py) is reused unchanged except for two things:
 * Engine. Its head engine is replaced by a parallel one (Lemma LZ, PROOF.md): a step opens the first element, builds
   spine(a) ++ [c, b·c], and every element below the consumed three ages by one pass. Aging is canonical:
   a normal form stays as it is (S, normal atoms OPQ/VAR/HOLE, applications S x y with normal parts, tokens of normal comb
   families); S a b ages to S P(a) P(b) (Lemma LZ (ii)); anything else gets a pending-pass node ("D", p, k) = P^k(p),
   which is forced (k passes of p's own run, recursively) only when it is opened. The unknown rest (junk) is never read,
   so its aging is irrelevant. Opening an atom-headed element fails, as before.
 * Concrete side. The concrete run is the lazy parallel run (code/lazy_par.py); snapshots are the values (all pending
   passes carried out) of the first elements.
Soundness: Lemma LZ's identities hold for all terms; OPQ/VAR stand for comb members F^j(X), so every loop (macro) is
accepted only for a normal comb family (X normal, F normal-preserving: F normal with its hole never applied to anything),
which makes the loop variable's instances normal forms. Everything else is as in Theorem LP (cycle lemma from W(n),
transient instance, numerical cross-check at every later cycle start). The whole-list (residue) pass ages pushed
segments, which is not implemented: it fails and the certificate is reported without a whole-list description.
Usage: python par_loop_prover.py TERM [TERM ...]"""
import sys
sys.setrecursionlimit(1000000)
import hc
import loop_prover as lp
from loop_prover import Fail, is_tok, is_seg, HOLE, JUNKSET, pmk
import lazy_par as lz
from par_vs_head import capped_pass
from symb import parse

def is_del(x): return isinstance(x, tuple) and x[0] == "D"

# ---- the pattern helpers, extended to pending-pass nodes ("D", p, k)
_o = {n: getattr(lp, n) for n in ("repl_atom", "contains", "subst", "shift", "inst", "diff", "abstract", "skel")}
def repl_atom(p, atom, v):
    return ("D", repl_atom(p[1], atom, v), p[2]) if is_del(p) else _o["repl_atom"](p, atom, v)
def contains(p, atom):
    return contains(p[1], atom) if is_del(p) else _o["contains"](p, atom)
def subst(p, v, var=lp.VAR):
    return ("D", subst(p[1], v, var), p[2]) if is_del(p) else _o["subst"](p, v, var)
def shift(p, d=1):
    return ("D", shift(p[1], d), p[2]) if is_del(p) else _o["shift"](p, d)
def inst(p, n):
    if is_del(p):
        t = inst(p[1], n)
        for _ in range(p[2]): t = capped_pass(10 ** 8)(t)
        return t
    if isinstance(p, tuple) and p[0] == "A": return hc.app(inst(p[1], n), inst(p[2], n))
    return _o["inst"](p, n)
def diff(prev, cur, occ):
    if is_del(prev) or is_del(cur):
        return is_del(prev) and is_del(cur) and prev[2] == cur[2] and diff(prev[1], cur[1], occ)
    return _o["diff"](prev, cur, occ)
def abstract(prev, cur, bmin, var=lp.VAR):
    if is_del(prev) and is_del(cur): return ("D", abstract(prev[1], cur[1], bmin, var), cur[2])
    return _o["abstract"](prev, cur, bmin, var)
def skel(p):
    return ("D", skel(p[1]), p[2]) if is_del(p) else _o["skel"](p)
for _n in ("repl_atom", "contains", "subst", "shift", "inst", "diff", "abstract", "skel"):
    setattr(lp, _n, globals()[_n])

# ---- normal forms
_nf = {}
def nf_int(x):
    """an hc pattern that is certainly a normal form (atoms other than junk count as normal forms; an application with an
    atom at its head does not, since the atom may stand for S x y)"""
    if x <= 0: return x not in JUNKSET
    r = _nf.get(x)
    if r is None:
        args, h = hc.spine(x)
        r = h == 0 and len(args) <= 2 and all(nf_int(a) for a in args)
        _nf[x] = r
    return r
_hh = {}
def hole_applied(F):
    if F <= 0: return False
    r = _hh.get(F)
    if r is None:
        r = hc.L[F] == HOLE or hole_applied(hc.L[F]) or hole_applied(hc.R[F]); _hh[F] = r
    return r
def fam_normal(F, X):
    """every F^j(X) is a normal form: X normal, F normal with its hole never in function position"""
    return isinstance(X, int) and nf_int(X) and nf_int(F) and not hole_applied(F)

# ---- the parallel engine
class ParEng(lp.Eng):
    def __init__(self):
        super().__init__(); self.fmemo = {}
    def spine(self, a):
        if is_del(a): return self.force(a[1], a[2])
        return super().spine(a)
    def age(self, x, k):
        if k == 0: return x
        if isinstance(x, int):
            if x in JUNKSET or nf_int(x): return x
        elif is_tok(x):
            if fam_normal(x[1], x[2]): return x
        elif is_del(x):
            return ("D", x[1], x[2] + k)
        elif is_seg(x):
            raise Fail("pushed segment ages")
        h, args = self.spine(x)
        if h == 0 and len(args) <= 2:                  # Lemma LZ (ii): P^k(S a b) = S P^k(a) P^k(b)
            r = 0
            for a in args: r = pmk(r, self.age(a, k))
            return r
        return ("D", x, k)
    def force(self, p, k):
        """head and argument list of P^k(p): k passes of p's own run"""
        r = self.fmemo.get((p, k))
        if r is not None: return r[0], list(r[1])
        h, args = self.spine(p)
        if h != 0: raise Fail("opaque head opened")
        stk = list(reversed(args)); done = 0
        while done < k:
            if len(stk) < 3:
                stk = [self.age(e, k - done) for e in stk]; done = k; break
            self.pstep(stk); done += 1
        r = (0, list(reversed(stk))); self.fmemo[(p, k)] = r
        return r[0], list(r[1])
    def pstep(self, stk):
        a, b, c = stk[-1], stk[-2], stk[-3]
        for x in (a, b, c):
            if isinstance(x, int) and x in JUNKSET: raise Fail("unknown rest reached")
            if is_seg(x): raise Fail("pushed segment reached")
        h, args = self.spine(a)
        if h != 0: raise Fail("opaque head opened")
        del stk[-3:]
        for i in range(len(stk)): stk[i] = self.age(stk[i], 1)
        stk.append(pmk(b, c)); stk.append(c); stk.extend(reversed(args))
        return len(args)
    def step(self, stk):
        if len(stk) < 3: raise Fail("hnf")
        n = self.pstep(stk); self.ops.append(n); return n
lp.Eng = ParEng

# loops only over normal comb families (their instances must be normal forms, as the atoms are)
_sm, _gm = lp.simple_macro, lp.general_macro
def simple_macro(eng, top, L, opq=lp.OPQ, var=lp.VAR):
    r = _sm(eng, top, L, opq, var)
    return r if r is None or fam_normal(r[3], r[4]) else None
def general_macro(eng, cur, hist, Lmax=170):
    r = _gm(eng, cur, hist, Lmax)
    return r if r is None or fam_normal(r[3], r[4]) else None
lp.simple_macro, lp.general_macro = simple_macro, general_macro

# ---- concrete side: the lazy parallel run, snapshots = values of the first K elements
K_SNAP = 14
NODE_CAP = 4_000_000                                   # values are materialised only on demand, within this table size
BUDGET = [None]                                        # table size at which the current materialisation gives up
_force = lz.force
def guarded_force(x, k):
    if len(lz.KIND) > NODE_CAP or (BUDGET[0] is not None and len(lz.KIND) > BUDGET[0]):
        raise Fail("concrete value too large")
    return _force(x, k)
lz.force = guarded_force
_canon = lz.canon
CALLS = [0]
def guarded_canon(x):
    if BUDGET[0] is not None:
        CALLS[0] += 1
        if CALLS[0] > 100_000 or len(lz.KIND) > BUDGET[0]: raise Fail("concrete value too large")
    return _canon(x)
lz.canon = guarded_canon
D2HC = {}
def d2hc(x):
    if x == 0: return 0
    r = D2HC.get(x)
    if r is None:
        if lz.KIND[x] != 1: raise Fail("pending pass left in a concrete value")
        r = hc.app(d2hc(lz.A[x]), d2hc(lz.B[x])); D2HC[x] = r
    return r
FAILED = {}                                            # lazy value -> the Fail its materialisation raised
GEN = [0]                                              # run generation: a reset invalidates older snapshots
class Snap:
    """the first K list elements at one pass, materialised (all pending passes carried out) when first read"""
    def __init__(self, entries, now): self.e = entries; self.now = now; self.v = {}; self.gen = GEN[0]
    def __len__(self): return len(self.e)
    def __getitem__(self, j):
        if isinstance(j, slice): return [self[i] for i in range(*j.indices(len(self.e)))]
        if j < 0: j += len(self.e)
        if j not in self.v:
            if self.gen != GEN[0]: raise Fail("stale snapshot")
            x, b = self.e[j]; d = lz.delay(x, self.now - b)
            if d in FAILED: v = FAILED[d]
            else:
                BUDGET[0] = len(lz.KIND) + 200_000; CALLS[0] = 0
                try:
                    v = d2hc(lz.canon(d))
                    if dag_over(v, VALUE_CAP): v = Fail("snapshot value too large")
                except Fail as e:
                    v = e
                finally:
                    BUDGET[0] = None
                if isinstance(v, Fail): FAILED[d] = v
            self.v[j] = v
        if isinstance(self.v[j], Fail): raise self.v[j]
        return self.v[j]
VALUE_CAP = 20_000                                     # DAG nodes; larger window values are evolving terms (no comb pattern)
def dag_over(t, cap):
    seen = set(); todo = [t]
    while todo:
        x = todo.pop()
        if x <= 0 or x in seen: continue
        seen.add(x)
        if len(seen) > cap: return True
        todo.append(hc.L[x]); todo.append(hc.R[x])
    return False
LAST = [None]
def par_run(src, N, snap_at=()):
    if LAST[0] != src or len(lz.KIND) > NODE_CAP // 2:   # the same term again: keep the table (values stay cached)
        lz.reset(); D2HC.clear(); FAILED.clear(); GEN[0] += 1; LAST[0] = src
    t = lz.from_tuple(parse(src)); stk = [(e, 0) for e in reversed(lz.plain_spine(t))]; ops = []; snaps = {}
    want = set(snap_at)
    for now in range(N):
        if now in want: snaps[now] = Snap(list(reversed(stk[-K_SNAP:])), now)
        if len(stk) < 3: return None, snaps
        (x1, b1), (x2, b2), (x3, b3) = stk.pop(), stk.pop(), stk.pop()
        v1, v2, v3 = lz.delay(x1, now - b1), lz.delay(x2, now - b2), lz.delay(x3, now - b3)
        c = lz.spine(v1); ops.append(len(c))
        stk.append((lz.app(v2, v3), now + 1)); stk.append((v3, now + 1)); stk.extend((e, now + 1) for e in reversed(c))
        if len(lz.KIND) > 6_000_000: return None, snaps
    return ops, snaps
lp.run = par_run

LAST_DELTA = [None]                                    # (a1, be1) of the last successful proof pass: anchor M1(n) is
_pc = lp.prove_cycle                                   # reached a1·n + be1 passes after the cycle start W(n)
def prove_cycle_stash(W, L, maxsteps=3000, exact_anchor=None):
    r = _pc(W, L, maxsteps, exact_anchor)
    if exact_anchor is None: LAST_DELTA[0] = (r[4][0], r[4][1])
    return r
lp.prove_cycle = prove_cycle_stash

def prove(src, N=60000):
    return lp.prove(src, N)

if __name__ == "__main__":
    for src in sys.argv[1:]:
        try:
            r = prove(src)
        except Fail as e:
            r = {"status": f"failed ({e})"}
        extra = ""
        if r["status"] == "PROVED":
            extra = (f"  (B = {r['B']}, {r['q']} loop(s) per cycle, window {r['window']}, cycle length {r['alpha']}·n + "
                     f"{r['beta']}, n >= {r['n0']}, {r['macros']} macro(s), first cycle {r['first_cycle']}, cross-check "
                     f"{r['crosscheck'][0]}/{r['crosscheck'][1]}, anchor {LAST_DELTA[0][0]}·n + {LAST_DELTA[0][1]})")
        print(f"{src}: parallel run {r['status']}{extra}", flush=True)
