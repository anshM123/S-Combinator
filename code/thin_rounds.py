"""Round anatomy of thin head runs (main agent, 2026-10-26).
A thin run keeps the second list element of spine <= 1. Rounds (Lemma R) run from one opcode-0 step to the next; round k
starts at [c_k, S c_k, d_k] ++ W. The round walks c_k's left spine with registers (u, v) = (S c_k, d_k):
  type 1 (S c'):           (u, v) <- (v, u·v)
  type 2 (S c' a):         push u·v;                 (u, v) <- (a, v)
  type k >= 3 (S c' a2..ak): push a4..ak, v, u·v;     (u, v) <- (a2, a3)
and ends at S with u = S (thinness of the next step). This prints, for the thin runs listed in FILE (one term per line),
the round kinds met in the second half of each run: start (Phi: d = S c; B: c = S(SSS)S; other), number m of type-1
steps, largest spine k in the walk, and the ending (E1: last step type 2 with a = S; E2: type 1 with v = S;
E3: type >= 3 with a2 = S). Usage: python thin_rounds.py FILE [STEPS]"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from symb import parse

def round_kind(c, d, B):
    u, v = hc.app(0, c), d
    x = c; m = 0; kmax = 0; last = None
    while x != 0:
        args, h = hc.spine(x); k = len(args); kmax = max(kmax, k)
        if k == 1:
            last = ("E2" if v == 0 else "t1"); u, v = v, hc.app(u, v); m += 1
        elif k == 2:
            last = ("E1" if args[1] == 0 else "t2"); u, v = args[1], v
        else:
            last = ("E3" if args[1] == 0 else "tk"); u, v = args[1], args[2]
        x = args[0]
    start = "Phi" if d == hc.app(0, c) else ("B" if c == B else "other")
    return (start, m, kmax, last)

if __name__ == "__main__":
    path = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 6000
    terms = [l.split()[0] for l in open(path, encoding="utf-8") if l.strip() and l.split()[0].startswith("S")]
    kinds = collections.Counter(); per_term = collections.Counter()
    for src in terms:
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()
        B = hc.from_tuple(parse("S(SSS)S"))
        args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; rounds = []; prev = None
        for n in range(N):
            if len(stk) < 3: break
            if prev == 0: rounds.append((stk[-1], stk[-3]))
            a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
            stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch)); prev = len(ch)
        tail = rounds[len(rounds) // 2:]
        ks = collections.Counter(round_kind(c, d, B) for c, d in tail)
        for k, v in ks.items(): kinds[k] += v
        per_term[tuple(sorted(ks))] += 1
    print(f"{len(terms)} thin runs; round kinds in the second half (start, m, max spine, ending): count")
    for k, v in kinds.most_common(): print(f"  {k}: {v}")
    print(f"distinct per-run round-kind sets: {len(per_term)}")
    for k, v in per_term.most_common(8): print(f"  {v:4d} runs: {list(k)}")
