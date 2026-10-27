"""Whole-list certificates for call-prover runs (main agent, 2026-10-26) — the call-run analogue of Corollary LP′.

The call prover (auto_prover.py) proves CALL: [L(d), a, b] ++ r ->* R(a·b) ++ ? and RESUME: [resume pattern(Z)] ++ r ->*
R(Z) ++ ?, leaving everything below the return form unknown. Here the same derivations are replayed exactly:
 * CALL  [L(d), a, b] ++ r -> R(a·b) ++ [RES(d, a, b)] ++ r, where RES(j, x, y) is the list between R(x·y) and the tape at
   the end of a level-j call: for levels covered by the inductive step it is read off the exact replay of the call step
   (in which inner calls and resumes leave their own RES/REM items); for the base levels it is computed concretely;
 * RESUME [pattern(Z)] ++ r -> R(Z) ++ [REM(d, Z)] ++ r, where REM is read off an exact run of the remainder of a level-(d+1)
   call from its resume point with the unknown rest directly below the top three (so the remainder must not read below
   them — if it does, no certificate is given);
 * driver: the exact replay of the driver derivation gives the residue D pushed between consecutive events, so the list at
   event k is R(G[L(k)]) ++ D(k-1) ++ D(k-2) ++ ... ++ (the concrete list at a base event).
Residue items never reach the top three during these replays (they stand for lists that are never read), so the replays
follow exactly the trajectories of the original proofs. Numerical test: at every observed driver event in the first N steps
the first K list entries predicted by this description (residues expanded recursively) equal the concrete ones.
Usage: python call_residue.py TERM..."""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
import auto_prover as ap
from auto_prover import JUNK, H
from symb import parse

def is_res(t): return isinstance(t, tuple) and len(t) >= 1 and t[0] in ("RES", "REM")

class Unsupported(Exception):
    pass

class XEngine(ap.Engine):
    """the call prover's engine with exact macros"""
    def __init__(self, sch, jmin, maxlev=10 ** 9, resume=None, resume_maxlev=10 ** 9):
        super().__init__(sch, jmin, maxlev, resume)
        self.resume_maxlev = resume_maxlev
    def run_exact(self, K, goal, cap=4000, call_first=False):
        for n in range(cap):
            if K[:3] == goal[:3]: return n, K
            if JUNK in K[:3] or any(is_res(t) for t in K[:3]): raise ValueError("rest or residue reached the top three")
            if not (call_first and n == 0):
                m = self.match_resume(K)
                if m and m[0] + 1 <= self.maxlev and self.jmin + m[0] + 1 >= 1 and m[0] <= self.resume_maxlev:
                    self.items.append(("resume", m[0] + 1))
                    K = self.s.R_of(m[1]) + [("REM", m[0], m[1])] + K[3:]; continue
            if self.s.is_tok(K[0]) and K[0][1] <= self.maxlev:
                d = K[0][1]
                if self.jmin + d < 0: raise ValueError("call at negative level")
                self.items.append(("call", d))
                K = self.s.R_of(self.s.mk(K[1], K[2])) + [("RES", d, K[1], K[2])] + K[3:]; continue
            ch = self.open_front(K[0]); self.items.append(("eng", len(ch)))
            K = ch + [K[2], self.s.mk(K[1], K[2])] + K[3:]
        return None, K

def below_top3(K):
    return K[3:K.index(JUNK)]

class Certificate:
    def __init__(self, src):
        self.src = src
        r = ap.prove(src)
        if r["status"] != "PROVED" or "_int" not in r: raise Unsupported("not proved by the call prover: " + r["status"])
        I = r["_int"]; self.I = I
        self.chain, self.F, self.i0, self.R = I["chain"], I["F"], I["i0"], I["R"]
        self.sch = ap.Scheme(self.F, self.R); self.res = I["res"]
        if self.res == "UNSAFE": raise Unsupported("resume unsafe")
        self.step_j = I["step_j"]
        self.levels = [m[2] for m in self.chain]
        self._derive()
    # ---------------------------------------------------------------- symbolic residues
    def _derive(self):
        sch = self.sch
        # RES: exact replay of the call step
        E = XEngine(sch, self.step_j, maxlev=-1, resume=self.res)
        K = [("L", 0), "x", "y", JUNK]
        first = E.open_front(K[0]); E.items.append(("eng", len(first)))
        K = first + [K[2], sch.mk(K[1], K[2])] + K[3:]
        n, Kend = E.run_exact(K, sch.R_of(("x", "y")))
        if n is None: raise Unsupported("call step replay did not reach the return form")
        self.RES = below_top3(Kend)
        # REM: the remainder of a level-1 call from its resume point, nothing below the top three known
        self.REM = None
        if self.res is not None:
            E0 = ap.Engine(sch, 3, maxlev=-10)
            K = [("L", 1), "x", "y", JUNK]
            for i in range(200):
                if sch.is_tok(K[0]) and K[0][1] == 0 and i > 0: break
                ch = E0.open_front(K[0]); K = ch + [K[2], sch.mk(K[1], K[2])] + K[3:]
            else:
                raise Unsupported("resume point not found")
            E1 = XEngine(sch, self.step_j, maxlev=0, resume=self.res, resume_maxlev=-1)
            try:
                n, Kend = E1.run_exact(K[:3] + [JUNK], sch.R_of(("x", "y")), call_first=True)
            except ValueError as e:
                raise Unsupported("remainder reads below the resume state's top three (" + str(e) + ")")
            if n is None: raise Unsupported("remainder replay did not return")
            self.REM = below_top3(Kend)
        # driver residue
        if self.I["drv_kind"] == "events":
            G = self.I["G"]; self.G = G
            y_only = ("Z" not in str(self.R)) and ("X" not in str(self.R))
            w0, w1 = sch.inst(G, ("L", 0)), sch.inst(G, ("L", 1))
            if y_only: w0, w1 = ("YONLY", w0), ("YONLY", w1)
            E2 = XEngine(sch, self.I["drv_j"], resume=self.res)
            n, Kend = E2.run_exact(sch.R_of(w0) + [JUNK], sch.R_of(w1))
            self.top_of = lambda k: sch.R_of(("YONLY", sch.inst(G, ("L", k))) if y_only else sch.inst(G, ("L", k)))
        else:
            T0 = self.I["T0"]
            E2 = XEngine(sch, self.I["drv_j"], resume=self.res)
            n, Kend = E2.run_exact([ap.shift_tok(t, 0) for t in T0] + [JUNK], [ap.shift_tok(t, 1) for t in T0])
            self.top_of = lambda k: [ap.shift_tok(t, k) for t in T0]
        if n is None: raise Unsupported("driver replay did not reach the next event")
        self.D = below_top3(Kend)
    # ---------------------------------------------------------------- concrete expansion
    def level(self, k):
        while len(self.levels) <= k: self.levels.append(ap.from_tuple_with(self.F, self.levels[-1]))
        if k < 0: raise Unsupported("negative level")
        return self.levels[k]
    def conc(self, t, base, env):
        """concrete hash-consed term for a symbolic term with level tokens relative to `base`"""
        if t == "S": return 0
        if t in env: return env[t]
        if self.sch.is_tok(t): return self.level(base + t[1])
        if isinstance(t, tuple) and len(t) == 2 and t[0] == "YONLY": return self.conc(t[1], base, env)
        if isinstance(t, tuple): return hc.app(self.conc(t[0], base, env), self.conc(t[1], base, env))
        raise Unsupported(f"cannot instantiate {t!r}")
    def concrete_residue(self, k):
        """list between the return form and the tape at the end of a concrete generic call of level k (atoms x=-1, y=-2)"""
        P = self.level(k); tape = [-6, -5, -4, -3]
        stk = tape + [-2, -1, P]; XY = hc.app(-1, -2)
        for t in range(2_000_000):
            a = stk[-1]; ch, h = hc.spine(a)
            if h != 0: break
            stk.pop(); bb = stk.pop(); cc = stk.pop()
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
        lst = stk[::-1]
        if lst[-4:] != tape[::-1]: raise Unsupported("generic call touched its tape")
        return lst[3:-4]
    def concrete_remainder(self, k):
        """REM at inner level k: the residue left by the remainder of a concrete generic level-(k+1) call from its resume
        point (first time the level-k term is the front). At that point everything below the top three is replaced by
        fresh opaque atoms; the remainder must return without any of them reaching the top three (barrier), and REM is the
        list above them at the return"""
        P = self.level(k + 1); tape = [-6, -5, -4, -3]
        stk = tape + [-2, -1, P]; inner = self.level(k)
        fresh = None
        for t in range(2_000_000):
            a = stk[-1]
            if t > 0 and a == inner and fresh is None:
                below = len(stk) - 3
                fresh = [-100 - i for i in range(below)]
                stk[:below] = fresh                          # bottom-first order; tape included
            if fresh is not None and any(x in fresh for x in stk[-3:]):
                raise Unsupported("concrete remainder reads below the resume state's top three")
            ch, h = hc.spine(a)
            if h != 0: break
            stk.pop(); bb = stk.pop(); cc = stk.pop()
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
        if fresh is None: raise Unsupported("resume point not reached")
        lst = stk[::-1]
        if lst[len(lst) - len(fresh):] != fresh[::-1]: raise Unsupported("remainder disturbed the lower items")
        return lst[3:len(lst) - len(fresh)]
    def subst_atoms(self, t, a, b):
        """replace the generic atoms x=-1, y=-2 by concrete terms"""
        memo = {}
        def go(u):
            if u == -1: return a
            if u == -2: return b
            if u <= 0: return u
            if u in memo: return memo[u]
            r = hc.app(go(hc.L[u]), go(hc.R[u])); memo[u] = r; return r
        return go(t)
    def expand(self, items, base, env, out, limit):
        for it in items:
            if len(out) >= limit: return
            if is_res(it):
                if it[0] == "RES":
                    _, d, a, b = it
                    ca, cb = self.conc(a, base, env), self.conc(b, base, env); lev = base + d
                    if lev - self.i0 >= self.step_j:
                        self.expand(self.RES, lev, {"x": ca, "y": cb}, out, limit)
                    else:
                        for u in self.concrete_residue(lev):
                            if len(out) >= limit: return
                            out.append(self.subst_atoms(u, ca, cb))
                else:
                    _, d, Z = it
                    cz = self.conc(Z, base, env); lev = base + d
                    if cz <= 0: raise Unsupported("resume product is not an application")
                    ca, cb = hc.L[cz], hc.R[cz]
                    if lev - self.i0 >= self.step_j and self.REM is not None:
                        self.expand(self.REM, lev, {"x": ca, "y": cb}, out, limit)
                    else:
                        for u in self.concrete_remainder(lev):
                            if len(out) >= limit: return
                            out.append(self.subst_atoms(u, ca, cb))
            else:
                out.append(self.conc(it, base, env))
    # ---------------------------------------------------------------- numerical whole-list test
    def check(self, N=300000, K=30):
        """events: driver events (R(G[L_k]) on top, or first appearances with template T0); predicted list at event k =
        top(k) ++ D(k-1) ++ D(k-2) ++ ... ++ concrete list below the top three at the base event"""
        tops = {}
        for k in range(len(self.chain), 0, -1): pass
        kmin = self.i0 + max(self.step_j, self.I["drv_j"]) + 1
        exp_top = {}
        for k in range(kmin, kmin + 30):
            try:
                t3 = tuple(self.conc(t, k, {}) for t in self.top_of(0)) if False else tuple(self.conc(t, k, {}) for t in self.top_of(0))
            except Unsupported:
                continue
            exp_top[t3] = k
        args, h = hc.spine(hc.from_tuple(parse(self.src))); stk = args[::-1]; snaps = {}
        for n in range(N):
            if len(stk) < 3: break
            key = (stk[-1], stk[-2], stk[-3])
            k = exp_top.get(key)
            if k is not None and k not in snaps: snaps[k] = stk[::-1][:K + 3]
            a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
        ks = sorted(snaps)
        if len(ks) < 2: return 0, 0
        kb = ks[0]; below_base = snaps[kb][3:]
        passed = total = 0
        for k in ks[1:]:
            pred = list(snaps[k][:3])
            for j in range(k - 1, kb - 1, -1):
                if len(pred) >= K: break
                self.expand(self.D, j, {}, pred, K)
            pred += below_base
            m = min(K, len(snaps[k]), len(pred))
            total += 1; passed += pred[:m] == snaps[k][:m]
        return passed, total

if __name__ == "__main__":
    for src in sys.argv[1:]:
        try:
            c = Certificate(src)
            p, t = c.check()
            print(f"{src}: whole list {'certified' if t and p == t else 'NOT certified'}  (call-step residue {len(c.RES)} items, "
                  f"remainder residue {'-' if c.REM is None else len(c.REM)} items, driver residue {len(c.D)} items; first 30 "
                  f"entries checked at {p}/{t} events)", flush=True)
        except (Unsupported, ValueError) as e:
            print(f"{src}: no whole-list certificate ({e})", flush=True)
