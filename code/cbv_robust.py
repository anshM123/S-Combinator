"""Which head runs are also call-by-value runs? (main agent, 2026-10-26)
Leftmost-innermost evaluation normalises the first three list elements before every head contraction. If in a head run
every element is a normal form whenever it is among the first three, the LI evolution performs exactly the head run (no
argument is ever evaluated), so LI contracts at the root forever. This scans the head runs used in robust_scan.py for
that property on their first N steps (a finite check, not a proof) and reports where it first fails.
Usage: python cbv_robust.py N"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from symb import parse
from robust_scan import has_redex, runs, _red

def cbv_ok(src, N):
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]
    for n in range(N):
        if len(stk) < 3: return "hnf"
        for e in stk[-3:]:
            if has_redex(e): return n
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return "ok"

if __name__ == "__main__":
    N = int(sys.argv[1]); tally = collections.Counter(); first = collections.Counter(); good = []
    for g, src in runs():
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear(); _red.clear()
        r = cbv_ok(src, N)
        tally[(g, "all top-three elements normal" if r == "ok" else ("hnf" if r == "hnf" else "a top-three element has a redex"))] += 1
        if isinstance(r, int): first[min(r, 99) // 10 * 10] += 1
        if r == "ok": good.append(src)
    for k, v in sorted(tally.items()): print(k, v)
    print("first failure step (bucketed by 10, capped at 99):", sorted(first.items()))
    print("runs that are LI runs at the root for all", N, "steps:", good[:20])
