"""Symbolic proof of the binary counter's driver, using the call lemma as a macro step (main agent).

Tokens ('P', d) denote P_{j+d} for a symbolic level j (assumed j >= JMIN). Derived: Q(d) = S S W P(d), R(d) = S Q(d),
U(d) = S S P(d) R(d); P_{m+1} = S U_m, P_0 = S L0.
Macro step: if the front element is a BARE token P(d) and at least two elements follow, the call lemma
(PROOF.md, 'The binary counter, exact') replaces [P(d), x, y | rest] by
  [x·y, V·(x·y), ((x·y)·(S·(x·y)))·(V·(x·y)), JUNK | rest]   after T_{j+d} = 2^(j+d+4) - 8 steps,
where JUNK marks the unknown rest of the list: the run fails if JUNK ever reaches the top three. Any other front element is opened by an ordinary head step
(a token as the head of a compound is unfolded one layer, requiring j + d >= 1).
Goal: from C1 at level j, [P(0), Q(0), P(0)·(S·P(0))·Q(0), JUNK], reach C1 at level j+1 without reading JUNK.
"""
import sys
sys.setrecursionlimit(1000000)
from symb import parse

b = parse("S(SS(SS))"); c = parse("S(S(SS)S)(SS(SS))"); W = ("S", "S"); V = parse("SS(SS)")
L0 = ((("S", "S"), b), c)
JMIN = 6

def P(d): return ("P", d)
def is_tok(t): return isinstance(t, tuple) and len(t) == 2 and t[0] == "P" and isinstance(t[1], int)
def Q(d): return ((("S", "S"), W), P(d))
def R(d): return ("S", Q(d))
def U(d): return ((("S", "S"), P(d)), R(d))
JUNK = "JUNK"

def is_U(t):
    return (isinstance(t, tuple) and not is_tok(t) and isinstance(t[0], tuple) and not is_tok(t[0])
            and t[0][0] == ("S", "S") and is_tok(t[0][1]) and t[1] == R(t[0][1][1]))

def mk(f, a):
    """application f·a in canonical form: S·U(d) is the token P(d+1) (P_{m+1} = S·U_m). Components are canonical,
    so only the root can be a new S·U redex-free pattern to fold."""
    if f == "S" and is_U(a): return P(a[0][1][1] + 1)
    return (f, a)

def spine(t):
    args = []
    while isinstance(t, tuple) and not is_tok(t):
        args.append(t[1]); t = t[0]
    args.reverse(); return t, args

def open_front(e):
    h, args = spine(e)
    if h == "S": return args
    if is_tok(h):
        d = h[1]
        if JMIN + d < 1: raise ValueError(f"level j{d:+d} may be 0 — raise JMIN")
        return [U(d - 1)] + args            # P_{j+d} = S U_{j+d-1}: spine [U(d-1)]
    raise ValueError(f"opaque element opened: {h}")

def show(t):
    if is_tok(t): return f"P{t[1]:+d}" if t[1] else "P"
    if t == "S" or isinstance(t, str): return t
    for name, v in (("W", W), ("V", V), ("b", b), ("c", c), ("L0", L0)):
        if t == v: return name
    for d in range(-3, 3):
        if t == Q(d): return f"Q{d:+d}" if d else "Q"
        if t == R(d): return f"R{d:+d}" if d else "R"
        if t == U(d): return f"U{d:+d}" if d else "U"
    h, args = spine(t)
    return show(h) + "".join("(" + show(a) + ")" if isinstance(a, tuple) or a not in ("S",) else "S" for a in args)

ITEMS = []   # trace of the last run: ("eng", opcode) | ("call", level offset) | ("resume", level offset)
MAXLEV = 10 ** 9   # macros (CALL at offset d, RESUME at parent offset d+1) are used only when that offset <= MAXLEV

def run(K, goal, max_macro=200, verbose=True):
    calls = []
    ITEMS.clear()
    for n in range(max_macro * 50):
        if K[:3] == goal[:3]:
            return n, calls
        if JUNK in K[:3]:
            raise ValueError("the unknown tail (JUNK) reached the top three - not determined by the lemmas")
        # macro 2 (continuation lemma): [P(d), W·P(d), (P(d)·R(d))·Z | r] is, in its top three, the state 6 steps into
        # a call P_{j+d+1}(x, y) with x·y = Z; the remainder never opens anything below the top three and ends after
        # T_{j+d+1} - 6 steps with [Z, V·Z, (Z·(S·Z))·(V·Z)] on top.
        if is_tok(K[0]) and len(K) >= 3:
            d = K[0][1]
            y = K[2]
            if (K[1] == (("S", "S"), P(d)) and isinstance(y, tuple) and not is_tok(y) and y[0] == (P(d), R(d))
                    and JMIN + d + 1 >= 1 and d + 1 <= MAXLEV):
                Z = y[1]
                calls.append((d + 1, "resume", show(Z))); ITEMS.append(("resume", d + 1))
                if verbose: print(f"  macro RESUME P{d + 1:+d} with x·y = {show(Z)[:70]}")
                K = [Z, mk(V, Z), mk(mk(Z, mk("S", Z)), mk(V, Z)), JUNK]
                continue
        if is_tok(K[0]) and len(K) >= 3 and K[0][1] <= MAXLEV:
            x, y = K[1], K[2]
            if JMIN + K[0][1] < 0: raise ValueError("call at a possibly negative level")
            xy = mk(x, y)
            calls.append((K[0][1], show(x), show(y))); ITEMS.append(("call", K[0][1]))
            if verbose: print(f"  macro CALL P{K[0][1]:+d}({show(x)[:40]}, {show(y)[:60]})")
            K = [xy, mk(V, xy), mk(mk(xy, mk("S", xy)), mk(V, xy)), JUNK]
            continue
        ch = open_front(K[0])
        ITEMS.append(("eng", len(ch)))
        K = ch + [K[2], mk(K[1], K[2])] + K[3:]
    return None, calls

if __name__ == "__main__":
    start = [P(0), Q(0), ((P(0), ("S", P(0))), Q(0)), JUNK]
    goal = [P(1), Q(1), ((P(1), ("S", P(1))), Q(1))]
    n, calls = run(start, goal)
    if n is None:
        print("goal NOT reached")
    else:
        print(f"C1(j) -> C1(j+1) reached after {n} engine steps and {len(calls)} macro calls, JUNK never read")
        print("calls (level offset, x, y):")
        for cl in calls: print("   ", cl)
