"""Check the Φ-regime theorem for unique-redex runs on concrete runs (main agent, 2026-10-26).
Theorem UR-R (PROOF.md), all sizes: in every infinite unique-redex head run, (a) at most three rounds after the first
opcode-0 step are not Φ-rounds (a Φ-round starts at [c, S c, S c]); (b) every later round is a Φ-round whose element c
has a left spine ending in B = S(SSS)S, A = SSS, S; (c) in a Φ-round with m type-1 steps the next element is
c' = S c (m = 0) or c' = S z (S^(m−1)(S c)) for some z (m ≥ 1); (d) each of the first m−1 type-1 steps is preceded by a
type-2 step with t = S. This script measures all four on the runs listed in FILE.
Usage: python ur_regime_check.py FILE [ROUNDS]"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from symb import parse

A = hc.from_tuple(parse("SSS")); B = hc.from_tuple(parse("S(SSS)S"))

def left_spine(c):
    """[(c_i, type, t_i)] down to S"""
    out = []
    while c != 0:
        args, h = hc.spine(c)
        out.append((c, len(args), args[1] if len(args) == 2 else None)); c = args[0]
    return out

def S_pow(j, x):
    for _ in range(j): x = hc.app(0, x)
    return x

if __name__ == "__main__":
    path = sys.argv[1]; NR = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    terms = [l.split()[1] for l in open(path, encoding="utf-8") if len(l.split()) > 2 and l.split()[1].startswith("S")]
    stats = collections.Counter(); ms = collections.Counter()
    for src in terms:
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()
        A = hc.from_tuple(parse("SSS")); B = hc.from_tuple(parse("S(SSS)S"))   # rebuilt after every table reset
        args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; rounds = []; prev = None
        for n in range(40000):
            if len(stk) < 3 or len(rounds) > NR: break
            if prev == 0: rounds.append((stk[-1], stk[-2], stk[-3]))
            a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch)); prev = len(ch)
        phi = [c2 == hc.app(0, c) and d == c2 for c, c2, d in rounds]
        first = next((i for i, p in enumerate(phi) if p), None)
        if first is None:
            stats["no Phi-round recorded"] += 1; continue
        stats["(a) non-Phi prefix <= 3"] += first <= 3 and all(phi[first:])
        ok_b = ok_c = ok_d = True
        for k in range(first, len(rounds) - 1):
            c = rounds[k][0]; c_next = rounds[k + 1][0]
            sp = left_spine(c)
            ok_b &= len(sp) >= 2 and sp[-2][0] == B and sp[-1][0] == A
            t1 = [i for i, (x, ty, t) in enumerate(sp) if ty == 1]; m = len(t1); ms[m] += 1
            if m == 0: ok_c &= c_next == hc.app(0, c)
            else:
                a2, h2 = hc.spine(c_next)
                ok_c &= h2 == 0 and len(a2) == 2 and a2[1] == S_pow(m - 1, hc.app(0, c))
            for j in t1[:-1]:
                ok_d &= j >= 1 and sp[j - 1][1] == 2 and sp[j - 1][2] == 0
        stats["(b) Phi-elements end in B, A, S"] += ok_b
        stats["(c) c' = S c or S z (S^(m-1)(S c))"] += ok_c
        stats["(d) type-1 steps before the last preceded by t = S"] += ok_d
    print(f"{path}: {len(terms)} terms")
    for k, v in stats.items(): print(f"  {k}: {v}/{len(terms)}")
    print("  type-1 steps per Phi-round (m):", dict(sorted(ms.items())))
