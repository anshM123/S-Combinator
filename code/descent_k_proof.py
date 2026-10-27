"""Theorem DK (the descending K-counter) — symbolic rules and per-term entry (main agent, 2026-10-26).
K = S(SS)(SS), Y_0 = K, Y_{n+1} = S S Y_n. A descent: the active list is exactly [S, S p q, c] (all normal); the head
step gives S c (S p q c), whose only redex is the argument, so the evolution continues with active list [p, q, c] and
c frozen outside. Rules, for opaque normal forms Y, Z, p, q:
  (D1) [S, S S Y, Z]  -> descent -> [S, Y, Z]
  (D2) [S, K, Z]      -> descent -> [SS, SS, Z]
  (D3) [SS, SS, Z]    -> [S, Z, S S Z] -> (Z = S p q) descent -> [p, q, S S Z]
Each rule is checked here on terms with opaque atoms (an atom is a normal form that is never opened), with exactly one
redex counted in every intermediate term. Then, for every term up to NMAX leaves whose one-redex evolution descends
at least N/2 times in N steps, the concrete evolution is followed (exactly one redex at every step, checked) until
the active list is [SS, SS, Y_n]; from there the rules give the rest for ever.
Usage: python descent_k_proof.py NMAX N [NMIN]"""
import sys
sys.setrecursionlimit(1000000)

# ---- symbolic part: terms are "S", atoms ("@", name), or pairs (f, x)
def is_atom(t): return isinstance(t, tuple) and t[0] == "@"
def args(t):
    out = []
    while isinstance(t, tuple) and not is_atom(t): out.append(t[1]); t = t[0]
    if t != "S": raise ValueError("opened an atom")
    return out[::-1]
def nred(t):
    if t == "S" or is_atom(t): return 0
    f, x = t
    head = f
    k = 1
    while isinstance(head, tuple) and not is_atom(head): head = head[0]; k += 1
    here = 1 if (head == "S" and k == 3) else 0
    return nred(f) + nred(x) + here
def app(*xs):
    t = xs[0]
    for x in xs[1:]: t = (t, x)
    return t
S = "S"; SS = app(S, S); K = app(S, SS, SS)

def sym_run(L, frozen=()):
    """head steps with descents until two descents happened or 6 steps; returns (list, frozen siblings, word)"""
    word = []; frozen = list(frozen)
    for _ in range(6):
        if len(L) < 3: raise ValueError("unexpected head normal form")
        if any(nred(e) for e in L): raise ValueError("second redex")
        a, b, c = L[0], L[1], L[2]
        new = args(a) + [c, (b, c)] + L[3:]
        word.append(len(args(a)))
        if len(new) >= 3:
            L = new; continue
        red = [e for e in new if nred(e)]
        if len(red) != 1 or nred(red[0]) != 1: raise ValueError("not exactly one redex after the step")
        frozen += [e for e in new if not nred(e)]
        return args(red[0]), frozen, word
    raise ValueError("no descent")

Y, Z, p, q = ("@", "Y"), ("@", "Z"), ("@", "p"), ("@", "q")
assert sym_run([S, app(S, S, Y), Z]) == ([S, Y, Z], [Z], [0])
assert sym_run([S, K, Z]) == ([SS, SS, Z], [Z], [0])
ZP = app(S, p, q)
assert sym_run([SS, SS, ZP]) == ([p, q, app(S, S, ZP)], [app(S, S, ZP)], [1, 0])
print("symbolic rules D1, D2, D3: OK (exactly one redex in every intermediate term)")

# ---- concrete part: entry of every forever-descending term into the K-cycle
import hc
from li_explore import has_redex, terms
from symb import parse
from descent_classify import family_index

def entry(t, N):
    """steps until the active list is [SS, SS, Y_n] (exactly one redex checked at each step), or None"""
    SSc = hc.from_tuple(parse("SS")); Kc = hc.from_tuple(parse("S(SS)(SS)"))
    L = list(hc.spine(t)[0]); descents = 0
    for n in range(N):
        while len(L) < 3:
            red = [e for e in L if has_redex(e)]
            if len(red) != 1: return None
            L = list(hc.spine(red[0])[0]); descents += 1
            if L[0] == SSc and L[1] == SSc and family_index(L[2], SSc, Kc) is not None:
                return n, descents, family_index(L[2], SSc, Kc)
        if any(has_redex(e) for e in L): return None
        a, b, c = L[0], L[1], L[2]
        L = list(hc.spine(a)[0]) + [c, hc.app(b, c)] + L[3:]
    return None

if __name__ == "__main__":
    if len(sys.argv) > 2:
        from descent_runs import evolve
        NMAX, N = int(sys.argv[1]), int(sys.argv[2]); NMIN = int(sys.argv[3]) if len(sys.argv) > 3 else 3
        total = proved = 0; worst = 0
        for n in range(NMIN, NMAX + 1):
            cnt = ok = 0
            for t in terms(n):
                steps, desc, v = evolve(t, N)
                if v != "alive" or len(desc) < N // 2: continue
                cnt += 1
                e = entry(t, N)
                if e is not None: ok += 1; worst = max(worst, e[0])
                else: print("   NOT PROVED:", hc.show(t), flush=True)
            total += cnt; proved += ok
            print(f"{n} leaves: {ok}/{cnt} forever-descending terms enter the K-cycle (then Theorem DK)", flush=True)
        print(f"{proved}/{total} PROVED by Theorem DK; latest entry at step {worst}")
