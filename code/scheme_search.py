"""Level-scheme search (main agent): which recursions can the call/continuation mechanism implement?
A term P is a CALL if the generic head run of [P, x, y, r1..r6] (atoms) gets stuck exactly when the front element is
x·y (the run hands control to the continuation x·y without having inspected x, y or r). A scheme is a context F (S-leaves
and holes H) with P_{m+1} = F[P_m]; for each base call P_0 and context F we test P_0..P_M and record the call times T_m.
Usage: python scheme_search.py NMAX M CAP OUT
"""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse

def trees_with_holes(n):
    """all binary trees with n leaves, each leaf 'S' or 'H' (at least one H)"""
    memo = {}
    def tr(n):
        if n in memo: return memo[n]
        if n == 1: out = ["S", "H"]
        else:
            out = []
            for i in range(1, n):
                for l in tr(i):
                    for r in tr(n - i): out.append((l, r))
        memo[n] = out; return out
    def has_h(t): return t == "H" or (isinstance(t, tuple) and (has_h(t[0]) or has_h(t[1])))
    return [t for t in tr(n) if has_h(t)]

def fill(F, X):
    if F == "H": return X
    if F == "S": return "S"
    return (fill(F[0], X), fill(F[1], X))

def spine(t):
    a = []
    while isinstance(t, tuple): a.append(t[1]); t = t[0]
    a.reverse(); return a, t

XY = ("x", "y")
def call_time(P, cap):
    stk = ["r6", "r5", "r4", "r3", "r2", "r1", "y", "x", P]
    for t in range(cap):
        if len(stk) < 3: return None
        a = stk[-1]
        args, h = spine(a)
        if h != "S":
            return t if a == XY else None
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        stk.append((bb, cc)); stk.append(cc); stk.extend(reversed(args))
    return None

def growth(T):
    d = [b - a for a, b in zip(T, T[1:])]
    if len(set(d)) == 1: return f"linear(+{d[0]})"
    dd = [b - a for a, b in zip(d, d[1:])]
    if len(set(dd)) == 1: return f"quadratic(dd={dd[0]})"
    # T_{m+1} = a T_m + c with integer a?
    for a in range(2, 9):
        cs = {T[i + 1] - a * T[i] for i in range(len(T) - 1)}
        if len(cs) == 1: return f"x{a}{'+' if list(cs)[0] >= 0 else ''}{list(cs)[0]}"
    r = [round(b / a, 3) for a, b in zip(T, T[1:]) if a]
    return "other " + str(r)

if __name__ == "__main__":
    NMAX, M, CAP, OUT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    b = parse("S(SS(SS))"); c = parse("S(S(SS)S)(SS(SS))")
    bases = {"SS": ("S", "S"), "S(SSbc)": ("S", ((("S", "S"), b), c))}
    found = collections.defaultdict(list); tested = 0
    for n in range(1, NMAX + 1):
        for F in trees_with_holes(n):
            for bn, P0 in bases.items():
                tested += 1
                T = []; P = P0
                for m in range(M + 1):
                    t = call_time(P, CAP)
                    if t is None: break
                    T.append(t); P = fill(F, P)
                if len(T) == M + 1 and T[-1] > T[-2]:
                    found[growth(T)].append((bn, F, T))
        print(f"n={n}: tested {tested}, growth classes so far: {sorted((k, len(v)) for k, v in found.items())[:12]}",
              flush=True)
    def show(t):
        if isinstance(t, str): return t
        l, r = t
        return show(l) + (("(" + show(r) + ")") if isinstance(r, tuple) else show(r))
    with open(OUT, "w", encoding="utf-8") as f:
        for g, L in sorted(found.items(), key=lambda kv: -len(kv[1])):
            f.write(f"## {g}: {len(L)} schemes\n")
            for bn, F, T in sorted(L, key=lambda x: len(show(x[1])))[:40]:
                f.write(f"   base {bn}  F = {show(F)}  T = {T}\n")
    print("classes:", {g: len(L) for g, L in found.items()})
