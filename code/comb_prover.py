"""Automatic exact proofs for comb (single-counter) head runs (main agent, 2026-10-26).

Pattern (found in the 12-leaf census): a loop whose blocks all start from [F, λ·T, E | r] and end at [F, T, E | r']
(one layer λ peeled off the second element per block, F and E unchanged), and a driver that, when the second element is
the base X_0, rebuilds the next loop start. Proof obligations, all checked here:
 (L) block lemma: from [F, λ·T, E | r] the head run reaches [F, T, E | r'] after |B| steps, for opaque T and r and for E
     either opaque or of the form λ·E' with E' opaque (whichever the run needs) — symbolic;
 (D) driver: with comb tokens C(d) = λ^{j+d}·X_0 (unfold C(d) = λ·C(d-1)), from [F, X_0, E(j)] to [F, C(1), E(j+1)],
     where E(j) is the third element at cycle j written as a comb over the same base (E = C(c)) — symbolic for all
     j >= JMIN, never reading the unknown rest;
 (T) transient: the concrete run reaches a cycle start [F, C_n, C_{n+c}] with n >= JMIN.
Then the run is, forever, loop of n blocks + driver, with n increasing by 1: its opcode word is D·B^n·D·B^{n+1}⋯ (morphic).
"""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
import hc

JUNK = "?"

def run_record(src, N):
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []; tops = []
    for n in range(N):
        if len(stk) < 3: return None, None
        tops.append((stk[-1], stk[-2], stk[-3]))
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(len(ch))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
        if len(hc.L) > 4_000_000: return None, None
    return ops, tops

def peel(t, lam):
    k = 0
    while t > 0 and hc.L[t] == lam: t = hc.R[t]; k += 1
    return k, t

def to_t(i):
    if i == 0: return "S"
    if i < 0: return f"a{-i}"
    return (to_t(hc.L[i]), to_t(hc.R[i]))

def block_lemma(F, lam, L, E_shape):
    """symbolic block of L steps; E_shape: 'opaque' or 'comb' (E = lam·E')"""
    Tv, Ev = -21, -22
    E = Ev if E_shape == "opaque" else hc.app(lam, Ev)
    stk = [-26, -25, -24, -23, E, hc.app(lam, Tv), F]
    for step in range(L):
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, hd = hc.spine(a)
        if hd != 0: return False
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return stk[::-1][:3] == [F, Tv, E]

def driver(F, X0, lam, c, jmin):
    LAM = to_t(lam); X0t = to_t(X0); Ft = to_t(F)
    def is_tok(t): return isinstance(t, tuple) and len(t) == 2 and t[0] == "C" and isinstance(t[1], int)
    def mk(f, a):
        if f == LAM and is_tok(a): return ("C", a[1] + 1)
        if f == LAM and a == X0t: return ("C", -10 ** 6)     # only meaningful as level 'j - j'; never used for j >= 1
        return (f, a)
    def unfold(t):
        if is_tok(t):
            if jmin + t[1] < 1: raise ValueError("comb level may be 0")
            return (LAM, ("C", t[1] - 1))
        return t
    def spine(t):
        xs = []
        while isinstance(t, tuple) and not is_tok(t): xs.append(t[1]); t = t[0]
        xs.reverse(); return t, xs
    K = [Ft, X0t, ("C", c), JUNK]; goal = [Ft, ("C", 1), ("C", c + 1)]; steps = 0
    for it in range(500):
        if K[:3] == goal: return steps
        if JUNK in K[:3]: raise ValueError("unknown rest reached")
        h0, xs = spine(unfold(K[0]))
        while is_tok(h0):
            h1, xs1 = spine(unfold(h0)); h0, xs = h1, xs1 + xs
        if h0 != "S": raise ValueError("opaque head opened")
        K = xs + [K[2], mk(K[1], K[2])] + K[3:]; steps += 1
    raise ValueError("goal not reached")

def prove(src, N=40000):
    ops, tops = run_record(src, N)
    if ops is None: return {"status": "run failed"}
    w = "".join(chr(48 + x) for x in ops)        # one character per step (opcodes >= 10 too)
    p = max(range(1, 40), key=lambda q: sum(w[i] == w[i - q] for i in range(q, len(w))))
    B0 = collections.Counter(w[i:i + p] for i in range(len(w) // 2, len(w) - p)).most_common(1)[0][0]
    last = {"status": "no aligned block structure", "B": B0}
    for rot in range(p):
        r = try_rotation(B0[rot:] + B0[:rot], w, tops)
        if r["status"] == "PROVED": return r
        last = r
    return last

def try_rotation(B, w, tops):
    starts = []; i = len(w) // 3
    while True:
        j = w.find(B * 4, i)
        if j < 0: break
        k = j
        while w.startswith(B, k): starts.append(k); k += len(B)
        i = k
    if len(starts) < 8: return {"status": "no long block runs", "B": B}
    F = tops[starts[0]][0]
    if any(tops[s_][0] != F for s_ in starts): return {"status": "front not constant at block starts", "B": B}
    sset = set(starts)
    inner = [s_ for s_ in starts if s_ + len(B) in sset]          # every block except the last of its run
    lefts = collections.Counter(hc.L[tops[s_][1]] for s_ in inner if tops[s_][1] > 0)
    if not lefts: return {"status": "second element not a layer", "B": B}
    lam = lefts.most_common(1)[0][0]
    if any(tops[s_][1] <= 0 or hc.L[tops[s_][1]] != lam for s_ in inner): return {"status": "layer not constant", "B": B}
    # (L)
    shape = "opaque" if block_lemma(F, lam, len(B), "opaque") else ("comb" if block_lemma(F, lam, len(B), "comb") else None)
    if shape is None: return {"status": "block lemma fails", "B": B}
    # cycle starts: first block of each run; X = C_n, E = comb over the same base
    # group block starts into runs of consecutive blocks; the loop start of a run is its block with the most layers in X
    runs_, cur = [], [starts[0]]
    for s_ in starts[1:]:
        if s_ == cur[-1] + len(B): cur.append(s_)
        else: runs_.append(cur); cur = [s_]
    runs_.append(cur)
    rel = []
    for run_ in runs_[1:-1]:
        best = max(run_, key=lambda s_: peel(tops[s_][1], lam)[0])
        kx, bx = peel(tops[best][1], lam); ke, be = peel(tops[best][2], lam)
        rel.append((best, kx, ke, bx, be))
    if any(r[3] != r[4] for r in rel) or len({r[2] - r[1] for r in rel}) != 1 or len({r[3] for r in rel}) != 1:
        return {"status": "cycle starts not combs over one base", "B": B}
    c = rel[0][2] - rel[0][1]; X0 = rel[0][3]
    if any(r2[1] != r1[1] + 1 for r1, r2 in zip(rel, rel[1:])): return {"status": "loop count does not grow by one", "B": B}
    # (D)
    for jmin in range(1, 6):
        try:
            dsteps = driver(F, X0, lam, c, jmin)
        except ValueError:
            continue
        # (T): the earliest cycle start with n >= jmin
        # with E_shape 'comb' the block lemma needs E = λ·E′ during the loop, i.e. at least one layer in E at the start
        first = next((r for r in rel if r[1] >= jmin and (shape == "opaque" or r[2] >= 1)), None)
        if first is None: return {"status": "no cycle start at a high enough level", "B": B}
        # cross-check: cycle n takes n·|B| + dsteps steps
        cc = [r2[0] - r1[0] == r1[1] * len(B) + dsteps for r1, r2 in zip(rel, rel[1:])]
        return {"status": "PROVED", "B": B, "layer_size": hc.size(lam), "c": c, "driver_steps": dsteps, "jmin": jmin,
                "E_shape": shape, "first_cycle": first[:2], "crosscheck": (sum(cc), len(cc))}
    return {"status": "driver not derived", "B": B}

if __name__ == "__main__":
    for src in sys.argv[1:]:
        r = prove(src)
        print(f"{src}: {r['status']}" + (f"  (B = {r['B']}, |λ| = {r['layer_size']}, E = C_(n+{r['c']}), driver {r['driver_steps']} steps, "
                                          f"j >= {r['jmin']}, first cycle {r['first_cycle']}, cross-check {r['crosscheck'][0]}/{r['crosscheck'][1]})"
                                          if r["status"] == "PROVED" else ""))
