"""Unique-redex S-terms (main agent, 2026-10-26).
If every list element of t = S e1 … en is a normal form, the only redex of t is the head redex. A head step
[a, b, c] ++ R => spine(a) ++ [c, b·c] ++ R creates one new element, b·c, which is a normal form iff b is S or S x
(b, c being normal forms). So t keeps a unique redex at every step for N steps iff its elements are normal forms and the
second element has spine length <= 1 at each of the first N steps. Such a term's multiway graph is a single path for N
steps: every evaluation order (leftmost-outermost, innermost, parallel, any strategy) performs the same evolution.
This enumerates all terms with up to NMAX leaves and reports those with the property for N steps and no hnf by then.
Usage: python unique_redex.py NMAX N [NMIN]"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from li_explore import has_redex, terms

def unique_run(t, N):
    args, h = hc.spine(t)
    if len(args) < 3 or any(has_redex(e) for e in args): return None
    stk = args[::-1]; ops = []
    for n in range(N):
        if len(stk) < 3: return None                      # head normal form: finite run
        if len(hc.spine(stk[-2])[0]) >= 2: return None    # b·c would be a redex
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        ops.append(len(ch))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return ops

if __name__ == "__main__":
    NMAX, N = int(sys.argv[1]), int(sys.argv[2])
    found = []
    NMIN = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    for n in range(NMIN, NMAX + 1):
        cnt = 0
        for t in terms(n):
            ops = unique_run(t, N)
            if ops is not None: found.append((n, hc.show(t), ops)); cnt += 1
        print(f"{n} leaves: {cnt} unique-redex runs of {N} steps", flush=True)
    for n, s, ops in found:
        print(n, s, "".join(map(str, ops[:80])))
