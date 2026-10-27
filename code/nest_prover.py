"""Nested-loop head runs (main agent, 2026-10-26) — extends loop_prover.py (Theorem LP) to loops whose blocks contain
inner loops.

Target: runs whose rounds repeat a block that itself contains a loop, e.g. the 'square' runs of E73 (round m = m
identical blocks X·Q^(m+c)·Y). New ingredients (all symbolic, for every n >= n0):
 * exact macros: a loop of m = n+b blocks maps A(F^m(X)) ++ r to A(X) ++ G(P, F, X, b) ++ r, where the segment
   G(P, F, X, b) = P(X) ++ P(F X) ++ ... ++ P(F^(m-1) X) holds the blocks' pushes (Lemma LB with pushes); the engine pops
   from a segment when it reaches the first three positions (n + b >= 1 recorded in n0);
 * nested block lemma: a block A(F(O)) ->* A(O) ++ P(O) whose symbolic run (O opaque, unknown rest below) may itself use
   loop macros on tokens in n — the block then takes tau(n) steps (a polynomial) instead of a fixed number;
 * loop detection across macros: the window is compared with every earlier window of the run (steps and macros);
 * step counts are polynomials in n; a loop of n+b blocks of tau(n) steps takes (n+b)·tau(n);
 * soundness of the cycle lemma: pass 1 (exact macros everywhere, unknown rest only below the cycle start) finds the
   closure M(n) ->* M(n+1) at anchor a; pass 2 repeats the run with the unknown rest directly below anchor a's window
   and must reach the same closure — so the cycle never reads below the anchor window (and pass 2 yields the residue);
 * rounds: cycle starts found as consecutive occurrences of a driver string between which the number of loop phases
   grows by one per round (square and countdown shapes), as well as the regular cycles of loop_prover.find_cycles.
Numerical cross-check: at the predicted times the concrete state is an instance of M(n) and of M(n+1).
"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
import loop_prover as lp
from loop_prover import (Fail, is_tok, is_seg, contains, pmk, fill, subst, shift, inst, min_offset, window, det_window,
                         with_junk, diff, abstract, skel, run, tokens, anti_window, toks_in, repl_atom, OPQ, VAR,
                         JUNKSET)

# ---------------------------------------------------------------- polynomials in n (coefficient tuples)
def padd(p, q):
    r = [0] * max(len(p), len(q))
    for i, c in enumerate(p): r[i] += c
    for i, c in enumerate(q): r[i] += c
    return tuple(r)
def psub(p, q): return padd(p, tuple(-c for c in q))
def pscale(p, c): return tuple(c * x for x in p)
def pmul_lin(p, b):
    """(n + b) · p(n)"""
    r = [0] * (len(p) + 1)
    for i, c in enumerate(p): r[i] += b * c; r[i + 1] += c
    return tuple(r)
def peval(p, n): return sum(c * n ** i for i, c in enumerate(p))
def pshow(p):
    t = [f"{c}" if i == 0 else (f"{c}·n" if i == 1 else f"{c}·n^{i}") for i, c in enumerate(p) if c]
    return " + ".join(reversed(t)) if t else "0"

def var_at(depth):
    """a distinct loop-variable atom per nesting depth (VAR, VAR-10, VAR-20): the pushes of an inner loop may then
    mention both its own variable and the variable of the loop it runs inside"""
    return VAR - 10 * depth

def opq_at(depth):
    """a distinct opaque atom per nesting depth, so an inner block lemma never confuses its own unknown with the
    unknown of the block lemma it runs inside"""
    return OPQ - depth

def subst_item(p, v, var):
    """replace the atom var by v in a pattern, or inside a segment's pushes (recursively); a segment's own variable is
    always a different atom, so it is never touched"""
    if is_seg(p): return ("G", tuple(subst_item(q, v, var) for q in p[1]), p[2], p[3], p[4], p[5])
    return subst(p, v, var)

def repl_item(q, atom, v):
    if is_seg(q): return ("G", tuple(repl_item(x, atom, v) for x in q[1]), q[2], q[3], q[4], q[5])
    return repl_atom(q, atom, v)

class Eng2(lp.Eng):
    """the loop prover's engine, popping from pushed segments ("G", P, F, X, b, w) — the list P(X) ++ P(F X) ++ ... with
    n + b groups, P written with its own variable atom w — when they reach the first three positions"""
    def expand_top(self, stk):
        while True:
            hit = None
            for i in (1, 2, 3):
                if len(stk) >= i and is_seg(stk[-i]): hit = len(stk) - i; break
            if hit is None: return
            _, P, F, X, b, w = stk[hit]
            if not P: del stk[hit]; continue                    # empty segment: a boundary marker only
            if 1 - b > 60: raise Fail("segment expanded too deep")
            self.n0 = max(self.n0, 1 - b)                       # the segment has at least one group
            grp = [subst_item(q, X, w) for q in P]
            stk[hit:hit + 1] = [("G", P, F, fill(F, X), b - 1, w)] + list(reversed(grp))
    def step(self, stk):
        self.expand_top(stk)
        return super().step(stk)

# ---------------------------------------------------------------- block lemmas and loop detection
class Mac(tuple):
    """a loop macro (A, h, b, F, X, tau, P, var), unpacked like a plain tuple; .word is one block's opcode word (ints
    for steps, ("L", mac) for inner loop macros), recorded from the block lemma's symbolic run — bookkeeping only"""
    def __new__(cls, fields, word):
        m = super().__new__(cls, fields); m.word = list(word); return m

def block_plain(A, F, Lb, depth):
    ok, sub, P = lp.block_lemma(A, F, Lb, opq_at(depth), var_at(depth))
    return ok, sub, (Lb,), P

def block_nested(A, F, L, depth, maxsteps=5000):
    """A(F(O)) ->* A(O) ++ P(O): symbolic run (unknown rest below) that may apply loop macros on tokens in n; O and the
    loop variable are the atoms of this depth, inner lemmas use their own"""
    h = len(A); O = opq_at(depth); V = var_at(depth)
    test = [subst(a, fill(F, O), V) for a in A]; expect = [subst(a, O, V) for a in A]
    sub = Eng2(); stk = with_junk(test); t = (0,); hist = []
    try:
        for it in range(maxsteps):
            win = window(stk)
            if it > 0 and win[:h] == expect:
                return True, sub, t, tuple(repl_item(q, O, V) for q in win[h:])
            if sub.n0 > 40: return False, sub, None, ()
            mac = find_macro(sub, stk, L, hist, depth + 1)
            if mac is not None:
                hist.append(("M", det_window(stk))); sub.ops.append(("L", mac))
                stk, dt = apply_exact(stk, mac); t = padd(t, dt); continue
            hist.append(("S", det_window(stk))); sub.step(stk); t = padd(t, (1,))
    except Fail:
        pass
    return False, sub, None, ()

def simple_macro2(eng, top, L, depth):
    m = lp.simple_macro(eng, top, L, opq_at(depth), var_at(depth))
    if m is None: return None
    A, h, b, F, X, Lb, P = m
    _, sub, _ = lp.block_lemma(A, F, Lb, opq_at(depth), var_at(depth))     # same deterministic run: its opcode word
    return Mac((A, h, b, F, X, (Lb,), P, var_at(depth)), sub.ops)

def general_macro2(eng, cur, hist, L, depth, Lmax=400):
    key = tuple(skel(x) for x in cur[:3]); V = var_at(depth)
    for back in range(1, min(Lmax, len(hist)) + 1):
        kind_prev, prev = hist[-back]
        if tuple(skel(x) for x in prev[:3]) != key: continue
        occ = []; h = 0
        while h < min(len(prev), len(cur)):
            o2 = []
            if not diff(prev[h], cur[h], o2): break
            occ += o2; h += 1
        if h < 3 or not occ or len({o[1:3] for o in occ}) != 1: continue
        F, X = occ[0][1], occ[0][2]; bmin = min(o[3] for o in occ)
        nested = any(k == "M" for k, _ in hist[-back:])
        if nested and depth >= 2: continue
        for hh in range(h, 2, -1):
            A = [abstract(prev[i], cur[i], bmin, V) for i in range(hh)]
            if not any(contains(a, V) for a in A): break
            if nested: ok, sub, tau, P = block_nested(A, F, L, depth)
            else: ok, sub, tau, P = block_plain(A, F, back, depth)
            if ok:
                eng.n0 = max(eng.n0, sub.n0, -bmin)
                return Mac((A, hh, bmin, F, X, tau, P, V), sub.ops)
    return None

def find_macro(eng, stk, L, hist, depth):
    pre = det_window(stk)
    return simple_macro2(eng, pre, L, depth) or general_macro2(eng, pre, hist, L, depth)

def apply_exact(stk, mac, junk_below=False):
    """m = n+b blocks: A(F^m X) ++ r -> A(X) ++ G(P, F, X, b) ++ r (r replaced by the unknown rest if junk_below)"""
    A, h, b, F, X, tau, P, var = mac
    below = [] if junk_below else window(stk)[h:]
    new = [subst(x, X, var) for x in A] + [("G", P, F, X, b, var)] + below
    return with_junk(new), pmul_lin(tau, b)

# ---------------------------------------------------------------- cycle lemma (two passes)
def prove_cycle2(W, L, junk_anchor=None, maxsteps=6000):
    eng = Eng2(); stk = with_junk(W); T = (0,); anchors = []; hist = []; at = []
    for it in range(maxsteps):
        if eng.n0 > 40: raise Fail("token unfolded too often")
        pre = det_window(stk)
        mac = find_macro(eng, stk, L, hist, 0)
        if mac is not None:
            A, h, b, F, X, tau, P, var = mac
            for ai, (A1, h1, b1, F1, X1, tau1, T1, var1) in enumerate(anchors):
                j = b - (b1 + 1)
                if (F, X) == (F1, X1) and h >= h1 and j >= 0 and A[:h1] == [shift(x) for x in A1]:
                    Tc = padd(psub(T, T1), pscale(tau, j))
                    R = None
                    if junk_anchor is not None:
                        after = [subst(x, ("T", F, X, b - j), var) for x in A]; pushes = []
                        for i in range(j, 0, -1): pushes += [subst_item(q, ("T", F, X, b - i), var) for q in P]
                        R = after[h1:] + pushes + window(stk)[h:]
                    # opcode word of one cycle M(n) ->* M(n+1): from anchor ai's macro on, then j blocks of this macro
                    word = eng.ops[at[ai]:] + [("J", mac, j)]
                    return dict(cycle=Tc, n0=eng.n0, anchor=ai, to_anchor=T1, word=word, to_anchor_word=eng.ops[:at[ai]],
                                M=[subst(x, ("T", F, X, b1), var1) for x in A1], R=R, macros=len(anchors))
            anchors.append((A, h, b, F, X, tau, T, var)); at.append(len(eng.ops)); eng.ops.append(("L", mac))
            hist.append(("M", pre))
            stk, dt = apply_exact(stk, mac, junk_below=(junk_anchor is not None and len(anchors) - 1 == junk_anchor))
            T = padd(T, dt); continue
        hist.append(("S", pre)); eng.step(stk); T = padd(T, (1,))
    raise Fail("cycle not closed")

# ---------------------------------------------------------------- rounds
def find_rounds(w):
    """cycle starts at consecutive occurrences of a driver string between which the number of loop phases grows by one"""
    scores = sorted(((sum(w[i] == w[i - p] for i in range(p, len(w))) / len(w), p) for p in range(1, 40)), reverse=True)
    out = []
    for sc, p in scores[:4]:
        B0 = collections.Counter(w[i:i + p] for i in range(len(w) // 2, len(w) - p)).most_common(1)[0][0]
        for r in range(p):
            B = B0[r:] + B0[:r]
            toks = tokens(w, B)
            ph = [(t[1], t[2], toks[i + 1][2]) for i, t in enumerate(toks[:-2]) if t[0] == "B" and toks[i + 1][0] == "D"]
            if len(ph) < 30: continue
            tail = ph[len(ph) // 4:]
            for D in {x[2] for x in tail}:
                idx = [i for i, x in enumerate(tail) if x[2] == D]
                if len(idx) < 6: continue
                gaps = [b2 - a2 for a2, b2 in zip(idx, idx[1:])]
                if all(g2 - g1 == 1 for g1, g2 in zip(gaps, gaps[1:])):
                    starts = [(tail[i + 1][0], g) for i, g in zip(idx, gaps) if i + 1 < len(tail)]
                    out.append((len(toks), B, starts))
    out.sort()
    return [(B, starts) for _, B, starts in out]

def prove(src, N=200000):
    ops, _ = run(src, N)
    if ops is None: return {"status": "run failed"}
    w = lp.opword(ops)
    cands = [(B, starts) for B, q, starts in lp.find_cycles(w)] + find_rounds(w)
    if not cands: return {"status": "no cycle or round structure"}
    first_fail = None; seen = set()
    for B, starts in cands[:12]:
        key = (B, tuple(starts[:3]))
        if key in seen: continue
        seen.add(key)
        r = prove_with(src, B, starts)
        if r["status"] == "PROVED": return r
        if first_fail is None: first_fail = r
    return first_fail

def prove_with(src, B, starts):
    L = len(B)
    if len(starts) < 5: return {"status": "too few cycles"}
    pos = [s for s, k in starts]
    _, snaps = run(src, pos[-1] + 1, snap_at=pos)
    last = {"status": "no pattern"}; tried = 0
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
                c1 = prove_cycle2(W, L)
                c2 = prove_cycle2(W, L, junk_anchor=c1["anchor"])       # soundness pass
                if (c2["cycle"], c2["anchor"]) != (c1["cycle"], c1["anchor"]): raise Fail("soundness pass differs")
                n0 = max([c2["n0"]] + [-min_offset(x) for x in W + c2["M"]])
            except Fail as e:
                last = {"status": f"cycle lemma fails ({e})"}; continue
            first = next(((s, n) for s, n in starts if n >= max(n0, 0)), None)
            if first is None: return {"status": "no cycle start with n >= n0"}
            if any(inst(W[j], first[1]) != snaps[first[0]][j] for j in range(wlen)):
                last = {"status": "transient instance fails"}; continue
            Tc, Ta, M = c2["cycle"], c2["to_anchor"], c2["M"]
            later = [(s, n) for s, n in starts if s >= first[0]]
            times = {}
            for s, n in later:
                t = s + peval(Ta, n); times[t] = n; times[t + peval(Tc, n)] = n + 1
            _, cs = run(src, max(times) + 1, snap_at=list(times))
            ok = [all(inst(M[j], times[t]) == cs[t][j] for j in range(len(M))) for t in sorted(times) if t in cs]
            return {"status": "PROVED", "B": B, "window": wlen, "cycle": Tc, "n0": n0, "macros": c2["macros"],
                    "first_cycle": first, "crosscheck": (sum(ok), len(times)), "residue": len(c2["R"] or []),
                    "word": c2["word"], "to_anchor_word": c2["to_anchor_word"], "to_anchor": Ta}
    return last

if __name__ == "__main__":
    for src in sys.argv[1:]:
        r = prove(src)
        extra = ""
        if r["status"] == "PROVED":
            extra = (f"  (B = {r['B'][:24]}{'…' if len(r['B']) > 24 else ''}, window {r['window']}, cycle length "
                     f"{pshow(r['cycle'])}, n >= {r['n0']}, {r['macros']} macro(s), first cycle {r['first_cycle']}, "
                     f"cross-check {r['crosscheck'][0]}/{r['crosscheck'][1]})")
        print(f"{src}: {r['status']}{extra}", flush=True)
