"""Parallel-robust infinite head runs (main agent): for terms from the 12-leaf census endpoints (binary counters, OTHER,
nested) and a sample of all hnf-free terms <= 10 leaves, compare the leftmost-outermost list-length sequence with the
parallel head-spine sequence over STEPS steps; a term is 'robust' if they agree at every step (by the transfer lemma this
holds when everything opened waits in normal form)."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse, trees, show
from lo_bt import cls, MF
import hc
from parallel_eval import step_fn
STEPS = int(sys.argv[1])
P = step_fn()
def compare(t):
    args, h = hc.spine(hc.from_tuple(t))
    lo = list(args); par = list(args)
    for n in range(STEPS):
        if len(lo) < 3 or len(par) < 3: return "hnf"
        a, b, c = lo[0], lo[1], lo[2]; ch, _ = hc.spine(a); lo = ch + [c, hc.app(b, c)] + lo[3:]
        a, b, c = par[0], par[1], par[2]; ch, _ = hc.spine(a); par = ch + [c, hc.app(b, c)] + [P(e) for e in par[3:]]
        if len(lo) != len(par) or lo[0] != par[0]: return n
        if len(hc.L) > 4_000_000: return "memory"
    return "robust"
census = [l.split("\t")[1] for l in open("../data/lo_census2_12.tsv", encoding="utf-8") if "\t" in l]
res = collections.Counter(); robust = []
for src in census:
    r = compare(parse(src)); key = r if isinstance(r, str) else "diverges"
    res[key] += 1
    if r == "robust": robust.append(src)
print(f"census binary/OTHER/nested endpoints ({len(census)}): {dict(res)}")
res2 = collections.Counter(); robust2 = []
for n in range(6, 11):
    for tt in trees(n):
        if MF[cls(tt)]: continue
        r = compare(tt); key = r if isinstance(r, str) else "diverges"
        res2[key] += 1
        if r == "robust": robust2.append(show(tt))
print(f"all hnf-free terms 6..10 leaves: {dict(res2)}")
print("robust examples:", (robust + robust2)[:15])
