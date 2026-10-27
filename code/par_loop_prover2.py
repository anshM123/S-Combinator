"""Parallel loop prover, lazy representation (main agent, 2026-10-26) — variant of par_loop_prover.py.
par_loop_prover.py compares the *values* of window elements, which blow up when an element contains a sub-term that keeps
evolving in parallel (never opened, but rewritten at every pass). Here pending passes stay in the patterns:
P^k(x) is written DK_k·x, an application of a special atom, so anti-unification, comb families and every pattern helper of
the loop prover work unchanged. One canonical aging rule is used both for the concrete snapshots and by the engine:
  age(x, k) = x                     if x is certainly a normal form (no redex, no pending pass, atoms normal)
            = S age(a, k) age(b, k)  if x = S a b or S a (Lemma LZ (ii))
            = DK_{j+k}·y            if x = DK_j·y
            = DK_k·x                otherwise.
Opening an element whose head is DK_k·y forces it (k passes of y's own run, Lemma LZ). Equal representations denote equal
terms, so a closing comparison that succeeds is sound; unequal representations of equal terms only make the prover fail.
Usage: python par_loop_prover2.py TERM [TERM ...]"""
import sys
sys.setrecursionlimit(1000000)
import hc
import par_loop_prover as plp                    # patches loop_prover (helpers, macros) — reused here
import loop_prover as lp
from loop_prover import Fail, is_tok, is_seg, JUNKSET, pmk
import lazy_par as lz
from symb import parse

DK0 = -10000
def DK(k): return DK0 - k
def is_dk(a): return isinstance(a, int) and a < DK0
def dk_k(a): return DK0 - a

nf_int = plp.nf_int
KMAX = 8                                               # an active element is evolved for at most KMAX passes to see if it settles

ORIG = plp.ParEng.__bases__[0]                    # loop_prover's own engine class (lp.Eng is patched by now)
class Plain(ORIG):
    """the loop prover's own spine (tokens unfolded, no forcing)"""
    pass

class ParEng2(ORIG):
    def __init__(self):
        super().__init__(); self.fmemo = {}
    def spine(self, a):
        h, args = ORIG.spine(self, a)
        if is_dk(h) and args:                           # (a bare DK_k inside a product: the caller appends its argument)
            h2, a2 = self.force(args[0], dk_k(h))
            return h2, a2 + args[1:]
        return h, args
    def pspine(self, a):
        p = Plain(); r = p.spine(a); self.n0 = max(self.n0, p.n0); return r
    def nf(self, x):
        if isinstance(x, int): return nf_int(x)
        if is_tok(x): return plp.fam_normal(x[1], x[2])
        if is_seg(x): return False
        h, args = self.pspine(x)
        return h == 0 and len(args) <= 2 and all(self.nf(a) for a in args)
    def age(self, x, k):
        """canonical P^k(x): a function of (x, k) only, so that aging pass by pass and aging once by the total agree"""
        if k == 0: return x
        if isinstance(x, int) and x in JUNKSET: return x
        if self.nf(x): return x
        if is_seg(x): raise Fail("pushed segment ages")
        h, args = self.pspine(x)
        if h == 0 and len(args) <= 2:
            r = 0
            for a in args: r = pmk(r, self.age(a, k))
            return r
        if is_dk(h) and len(args) == 1: return self.age_active(args[0], dk_k(h) + k)
        return self.age_active(x, k)
    def age_active(self, x, k):
        """P^k(x) for x with a redex or pending pass at its head: its normal form if it reaches one within min(k, KMAX)
        passes, else DK_k·x"""
        try:
            h, args = self.force(x, min(k, KMAX))
            r = 0
            for a in args: r = pmk(r, a)
            if h == 0 and self.nf(r): return r
        except Fail:
            pass                                       # cannot tell symbolically: keep the pass pending (still exact)
        return pmk(DK(k), x)
    def force(self, p, k):
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
lp.Eng = ParEng2
CE = ParEng2()                                         # the same aging rule for concrete snapshots (no atoms there)

# ---- concrete side: snapshots in the same canonical lazy representation (no pending pass is carried out)
CONV = {}
def conv(d):
    if d == 0: return 0
    r = CONV.get(d)
    if r is None:
        if lz.KIND[d] == 1: r = hc.app(conv(lz.A[d]), conv(lz.B[d]))
        else: r = CE.age(conv(lz.A[d]), lz.B[d])
        CONV[d] = r
    return r
class Snap2:
    def __init__(self, entries, now): self.e = entries; self.now = now; self.v = {}; self.gen = plp.GEN[0]
    def __len__(self): return len(self.e)
    def __getitem__(self, j):
        if isinstance(j, slice): return [self[i] for i in range(*j.indices(len(self.e)))]
        if j < 0: j += len(self.e)
        if j not in self.v:
            if self.gen != plp.GEN[0]: raise Fail("stale snapshot")
            x, b = self.e[j]; v = conv(lz.delay(x, self.now - b))
            if plp.dag_over(v, plp.VALUE_CAP): raise Fail("snapshot value too large")
            self.v[j] = v
        return self.v[j]
LAST = [None]
def par_run2(src, N, snap_at=()):
    if LAST[0] != src or len(lz.KIND) > plp.NODE_CAP // 2:
        lz.reset(); CONV.clear(); CE.fmemo.clear(); plp.GEN[0] += 1; LAST[0] = src
    t = lz.from_tuple(parse(src)); stk = [(e, 0) for e in reversed(lz.plain_spine(t))]; ops = []; snaps = {}
    want = set(snap_at)
    for now in range(N):
        if now in want: snaps[now] = Snap2(list(reversed(stk[-plp.K_SNAP:])), now)
        if len(stk) < 3: return None, snaps
        (x1, b1), (x2, b2), (x3, b3) = stk.pop(), stk.pop(), stk.pop()
        v1, v2, v3 = lz.delay(x1, now - b1), lz.delay(x2, now - b2), lz.delay(x3, now - b3)
        c = lz.spine(v1); ops.append(len(c))
        stk.append((lz.app(v2, v3), now + 1)); stk.append((v3, now + 1)); stk.extend((e, now + 1) for e in reversed(c))
        if len(lz.KIND) > plp.NODE_CAP: return None, snaps
    return ops, snaps
lp.run = par_run2

# instances of patterns are compared in the same representation: DK atoms stay atoms (no pass is carried out)
lp.inst = plp._o["inst"]

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
                     f"{r['crosscheck'][0]}/{r['crosscheck'][1]}, anchor {plp.LAST_DELTA[0][0]}·n + {plp.LAST_DELTA[0][1]})")
        print(f"{src}: parallel run {r['status']}{extra}", flush=True)
