"""Follow-up on lo_census2_12.tsv (main agent): (1) radix law of every OTHER endpoint (rand_radix.radix over 60k steps);
(2) does every binary-counter endpoint reach C1(k) of SSS(SS)S(SS(SS)) (same machine)?"""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
from rand_radix import opseq, radix
import hc
rows = [l.rstrip("\n").split("\t") for l in open("../data/lo_census2_12.tsv", encoding="utf-8") if "\t" in l]
other = [r[1] for r in rows if r[0] == "OTHER"]; binary = [r[1] for r in rows if r[0] == "binary counter"]
nested = [r[1] for r in rows if r[0] == "nested counter"]
print(f"OTHER {len(other)}, binary {len(binary)}, nested {len(nested)}")
rad = collections.Counter()
for s in other:
    seq = opseq(parse(s), 60000)
    r = radix(seq) if seq else None
    rad[r[0] if r else None] += 1
    print(f"  OTHER {s:45s} radix: {('base %d op %d gaps %s freq %s' % r) if r else 'none'}", flush=True)
print("OTHER radix summary:", dict(rad))
# same machine test for binary counters: front element equal to a level P_k with C1(k) on top
from symb import parse as P_
b = P_("S(SS(SS))"); c = P_("S(S(SS)S)(SS(SS))"); W = ("S", "S")
L0 = ((("S", "S"), b), c)
Pk = [("S", L0)]
for m in range(12):
    Rm = ("S", ((("S", "S"), W), Pk[m])); Um = ((("S", "S"), Pk[m]), Rm); Pk.append(("S", Um))
C1 = []
for k in range(12):
    Q = ((("S", "S"), W), Pk[k]); C1.append([hc.from_tuple(Pk[k]), hc.from_tuple(Q), hc.from_tuple(((Pk[k], ("S", Pk[k])), Q))])
lev = {C1[k][0]: k for k in range(12)}
same = 0; notsame = []
for s in binary:
    args, h = hc.spine(hc.from_tuple(parse(s))); stk = args[::-1]; hit = None
    for n in range(20000):
        if len(stk) < 3: break
        a = stk[-1]
        if a in lev and stk[-1:-4:-1] == C1[lev[a]] and lev[a] >= 2: hit = (n, lev[a]); break
        stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    if hit: same += 1
    else: notsame.append(s)
print(f"binary counters reaching C1(k>=2) of the known machine within 20k steps: {same} of {len(binary)}")
for s in notsame[:20]: print("   not the known machine (within 20k):", s)
