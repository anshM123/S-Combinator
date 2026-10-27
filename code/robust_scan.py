"""How many head runs are parallel-robust? (main agent, 2026-10-26)
By Lemma PH a parallel (ReplaceAll) pass is one head step plus one pass inside every list element below the first three.
If every element below the first three is a normal form at every step, the parallel evolution equals the head run step
for step. This scan checks that condition on the first N steps of each run (a necessary condition; finite, not a proof).
Usage: python robust_scan.py N   (runs: the 150-run census sample, the 152 counters, the 13–16 and 17–24 samples)"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from symb import parse

_red = {}
def has_redex(i):
    """does the term contain a subterm S x y z?"""
    if i <= 0: return False
    r = _red.get(i)
    if r is None:
        args, h = hc.spine(i)
        r = (h == 0 and len(args) >= 3) or has_redex(hc.L[i]) or has_redex(hc.R[i])
        _red[i] = r
    return r

def robust(src, N):
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]
    for n in range(N):
        if len(stk) < 3: return "hnf"
        for e in stk[:-3]:                       # everything below the first three (stk is top-last)
            if has_redex(e): return f"redex below the top three at step {n}"
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
        if len(hc.L) > 3_000_000: return "memory"
    return "robust"

def runs():
    out = []
    for l in open("../data/sample_union_150.tsv", encoding="utf-8"):
        if l.strip(): out.append(("census sample", l.split("\t")[0]))
    for l in open("../data/lo_census2_12.tsv", encoding="utf-8"):
        if "\t" in l: out.append(("counters", l.split("\t")[1]))
    for fn, g in (("../data/sample_large_13_16.tsv", "13-16"), ("../data/sample_hunt_17_24.tsv", "17-24")):
        for l in open(fn, encoding="utf-8"):
            if l.strip(): out.append((g, l.split("\t")[0]))
    return out

if __name__ == "__main__":
    N = int(sys.argv[1]); tally = collections.Counter(); first = collections.Counter()
    for g, src in runs():
        hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear(); _red.clear()
        r = robust(src, N)
        tally[(g, "robust" if r == "robust" else "not robust")] += 1
        if r.startswith("redex"): first[int(r.split()[-1]) // 100 * 100] += 1
    for k, v in sorted(tally.items()): print(k, v)
    print("first non-normal element below the top three, by step (bucketed):", sorted(first.items())[:12])
