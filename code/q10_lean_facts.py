"""Finite facts for a Lean formalisation of Theorem Q10 (main agent, 2026-10-27), checked here first.
M35 (data/model35_hn.txt): s = class 0, F = HN classes.
 (F2) no product a·b equals s.
 (F3) right-multiplication graph a -> a·b without self-loops is acyclic; the only self-loop at an F class is 12·s = 12.
      rank(a) = longest path to a sink. Lean needs: for a in F and all b, a·b = a (only 12·s) or rank(a·b) < rank(a);
      and "not F" is left-absorbing (a·b in F => a in F).
 (F4) chain graph on states (a, b, beta) with s·a·b·beta in F:
      peel   (a, b, beta) -> (x, beta, b·beta)   for every x with s·x = a,
      refill (a, b, beta) -> (a2, b2, b·beta)    for every (a2, b2) with s·a2·b2 = a·beta, b2 != s, when a in PRE
             (PRE = classes of terms with >= 2 arguments; variant ALL: every a != s, an over-approximation).
      Lean needs an index g with g strictly decreasing along every edge except peel self-loops, and no refill self-loop.
Prints the facts and writes the rank and index tables used by the Lean file. Usage: python q10_lean_facts.py [PRE|ALL]"""
import sys, collections
from verify_model import load
reps, F, T = load("../data/model35_hn.txt")
n = len(reps); s = 0
mul = lambda a, b: int(T[a, b])
inF = [bool(F[k]) for k in range(n)]
mode = sys.argv[1] if len(sys.argv) > 1 else "PRE"

f2 = all(mul(a, b) != s for a in range(n) for b in range(n))
absorb = all((not inF[mul(a, b)]) or inF[a] for a in range(n) for b in range(n))
selfloops = [(a, b) for a in range(n) for b in range(n) if inF[a] and mul(a, b) == a]
# rank: longest path in the right-multiplication graph without self-loops
adj = {a: {mul(a, b) for b in range(n) if mul(a, b) != a} for a in range(n)}
rank = {}
def rk(a, stack=()):
    if a in rank: return rank[a]
    if a in stack: raise ValueError("cycle in right-multiplication graph")
    r = max((rk(c, stack + (a,)) + 1 for c in adj[a]), default=0)
    rank[a] = r; return r
for a in range(n): rk(a)
rank_ok = all(mul(a, b) == a or rank[mul(a, b)] < rank[a] for a in range(n) if inF[a] for b in range(n))
print(f"F2 (no product is s): {f2}; not-F left-absorbing: {absorb}; F self-loops: {selfloops}; "
      f"max rank {max(rank.values())}; rank strictly decreases off self-loops (a in F): {rank_ok}")

PRE = {mul(mul(s, x), y) for x in range(n) for y in range(n)}
changed = True
while changed:
    changed = False
    for p in list(PRE):
        for e in range(n):
            if mul(p, e) not in PRE: PRE.add(mul(p, e)); changed = True
DEC = collections.defaultdict(list)
for a2 in range(n):
    for b2 in range(n):
        if b2 != s: DEC[mul(mul(s, a2), b2)].append((a2, b2))
SX = collections.defaultdict(list)
for x in range(n): SX[mul(s, x)].append(x)
states = [(a, b, be) for a in range(n) for b in range(n) for be in range(n) if inF[mul(mul(mul(s, a), b), be)]]
edges = collections.defaultdict(set); peel_self = 0; refill_self = 0
for (a, b, be) in states:
    for x in SX.get(a, ()):
        t = (x, be, mul(b, be))
        if t == (a, b, be): peel_self += 1
        else: edges[(a, b, be)].add(t)
    if a != s and (mode == "ALL" or a in PRE):
        for (a2, b2) in DEC.get(mul(a, be), ()):
            t = (a2, b2, mul(b, be))
            if t == (a, b, be): refill_self += 1
            else: edges[(a, b, be)].add(t)
# longest-path index (fails on a cycle)
sys.setrecursionlimit(1000000)
g = {}; onstack = set()
def gi(v):
    if v in g: return g[v]
    if v in onstack: raise ValueError(f"cycle through {v}")
    onstack.add(v)
    r = max((gi(w) + 1 for w in edges.get(v, ()) if w in set_states), default=0)
    onstack.discard(v); g[v] = r; return r
set_states = set(states)
outside = sum(1 for v in states for w in edges.get(v, ()) if w not in set_states)
try:
    for v in states: gi(v)
    acyclic = True
except ValueError as e:
    acyclic = False; print("CYCLE:", e)
print(f"[{mode}] states {len(states)}, edges {sum(len(v) for v in edges.values())}, edges leaving the state set {outside}; "
      f"peel self-loops {peel_self}, refill self-loops {refill_self}; acyclic off peel self-loops: {acyclic}; "
      f"max index {max(g.values()) if g else None}")
if acyclic and mode == sys.argv[1:2][0] if len(sys.argv) > 1 else acyclic:
    with open(f"../data/q10_tables_{mode}.txt", "w") as fh:
        fh.write("rank " + " ".join(str(rank[a]) for a in range(n)) + "\n")
        for (a, b, be) in states: fh.write(f"g {a} {b} {be} {g[(a, b, be)]}\n")
    print(f"tables written to data/q10_tables_{mode}.txt")
