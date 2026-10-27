"""Coverage of the 12-leaf census's counter endpoints by the proved theorems (main agent): for every binary/OTHER/nested
endpoint in data/lo_census2_12.tsv, run 60,000 head steps and check whether the top three ever equal C1(k) of Theorem BC
(k >= 2) or R'(M_k) of Theorem BC2 (k >= 2); then the theorem's driver proves the rest of the run."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
import hc
# Theorem BC levels and C1
b = parse("S(SS(SS))"); c = parse("S(S(SS)S)(SS(SS))"); W = ("S", "S")
P = [("S", ((("S", "S"), b), c))]
for m in range(12):
    Rm = ("S", ((("S", "S"), W), P[m])); Um = ((("S", "S"), P[m]), Rm); P.append(("S", Um))
BC = {}
for k in range(2, 12):
    Q = ((("S", "S"), W), P[k]); top = [hc.from_tuple(P[k]), hc.from_tuple(Q), hc.from_tuple(((P[k], ("S", P[k])), Q))]
    BC[top[0]] = (k, top)
# Theorem BC2 levels and R'(M_k)
L = [hc.from_tuple(parse("S(S(S(S(SSS)))S)"))]
for m in range(12): Lk = L[-1]; L.append(hc.app(0, hc.app(hc.app(0, Lk), hc.app(Lk, hc.app(0, Lk)))))
BC2 = {}
for k in range(2, 12):
    Mk = hc.app(hc.app(0, L[k]), hc.app(L[k], hc.app(0, L[k])))
    E = hc.app(Mk, hc.app(0, Mk)); top = [E, hc.app(0, E), hc.app(hc.app(0, Mk), E)]
    BC2[E] = (k, top)
rows = [l.rstrip("\n").split("\t") for l in open("../data/lo_census2_12.tsv", encoding="utf-8") if "\t" in l]
cov = collections.Counter(); unc = collections.defaultdict(list)
for cls_, src, *_ in rows:
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; hit = None
    for n in range(60000):
        if len(stk) < 3: break
        a = stk[-1]
        if a in BC and stk[-1:-4:-1] == BC[a][1]: hit = "Theorem BC"; break
        if a in BC2 and stk[-1:-4:-1] == BC2[a][1]: hit = "Theorem BC2"; break
        stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    cov[(cls_, hit or "not covered")] += 1
    if not hit and len(unc[cls_]) < 6: unc[cls_].append(src)
for k, v in sorted(cov.items()): print(f"{k[0]:16s} {k[1]:14s} {v}")
for k, v in unc.items(): print("uncovered examples", k, v)
