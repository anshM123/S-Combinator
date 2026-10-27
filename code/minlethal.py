"""Minimal non-productive terms (all proper subterms productive, the term not), by the 39-class model, up to N leaves."""
import sys
from collections import Counter
from verify_model import load
from symb import trees, show, spine
reps, F, P = load("../data/model39_productivity.txt")
M_reps, M_F, M = load("../data/model35_hn.txt")
s, sM = reps.index("S"), M_reps.index("S")
memo, memoM = {}, {}
def cl(t):
    if t == "S": return s
    if t in memo: return memo[t]
    r = int(P[cl(t[0]), cl(t[1])]); memo[t] = r; return r
def clM(t):
    if t == "S": return sM
    if t in memoM: return memoM[t]
    r = int(M[clM(t[0]), clM(t[1])]); memoM[t] = r; return r
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10
for n in range(2, N + 1):
    mins = [t for t in trees(n) if not F[cl(t)] and F[cl(t[0])] and F[cl(t[1])]]
    hn = Counter("no-hnf" if not M_F[clM(t)] else "hnf" for t in mins)
    heads = Counter(len(spine(t)[1]) for t in mins)
    print(f"n={n}: minimal non-productive {len(mins)}  ({dict(hn)})  spine-arity histogram {dict(sorted(heads.items()))}")
    for t in mins[:4 if n <= 9 else 2]: print("     ", show(t), "| M35:", "no hnf" if not M_F[clM(t)] else "hnf")
