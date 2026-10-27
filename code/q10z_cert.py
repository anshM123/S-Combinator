"""Structure report / certificate attempt for 'open Q10' on a learned model of head normalisation over {S, z}.

Checks: (G1) S-identity; (G2) S, S x, S x y in F and every z-headed product (closure of [z] under right
multiplication) in F; (G3) bottom classes left-absorbing; (G4) no product equals [S].
Then: SCCs of the right-multiplication graph on F classes (minus self-loops), self-loops, the stuck class sigma = [z],
and the tail-chain graph (peel / refill edges as in Theorem Q10) on states (a, b, e) with s.a.b.e in F.
Usage: python q10z_cert.py MODELFILE
"""
import sys, collections
import networkx as nx
from verify_model import load

reps, F, M = load(sys.argv[1])
n = len(reps); s = 0; zc = 1
mul = lambda x, y: int(M[x, y])
Fset = [i for i in range(n) if F[i]]; bots = [i for i in range(n) if not F[i]]
print(f"classes {n}, F {len(Fset)}, bottom {bots}, [S] = {s} ({reps[s]}), [z] = {zc} ({reps[zc]})")
g1 = sum(1 for x in range(n) for y in range(n) for z in range(n) if mul(mul(mul(s, x), y), z) != mul(mul(x, z), mul(y, z)))
g2a = all(F[s]) if False else (F[s] and all(F[mul(s, x)] for x in range(n)) and all(F[mul(mul(s, x), y)] for x in range(n) for y in range(n)))
stuck = {zc}; fr = [zc]
while fr:
    a = fr.pop()
    for b in range(n):
        c = mul(a, b)
        if c not in stuck: stuck.add(c); fr.append(c)
g2b = all(F[c] for c in stuck)
g3 = all(mul(b, x) in bots for b in bots for x in range(n))
g4 = all(mul(x, y) != s for x in range(n) for y in range(n))
print(f"(G1) S-identity violations {g1}; (G2) values in F: S-hnfs {g2a}, z-headed closure {sorted(stuck)} all F {g2b}; "
      f"(G3) bottom left-absorbing {g3}; (G4) no product equals [S] {g4}")
RM = nx.DiGraph(); RM.add_nodes_from(range(n))
loops = collections.defaultdict(list)
for a in range(n):
    for b in range(n):
        c = mul(a, b)
        if c != a: RM.add_edge(a, c)
        elif F[a]: loops[a].append(b)
sccs = [c for c in nx.strongly_connected_components(RM) if len(c) > 1]
print(f"right-multiplication graph minus self-loops: nontrivial SCCs {[sorted(c) for c in sccs]}")
print("self-loops at F classes (class: multipliers):", {a: (v if len(v) < 8 else f'{len(v)} classes') for a, v in loops.items()})
one = collections.defaultdict(list); two = collections.defaultdict(list)
for x in range(n):
    one[mul(s, x)].append(x)
    for y in range(n):
        two[mul(mul(s, x), y)].append((x, y))
G = nx.DiGraph(); kind = {}
states = [(a, b, e) for a in range(n) for b in range(n) for e in range(n) if F[mul(mul(mul(s, a), b), e)]]
S_ = set(states)
for (a, b, e) in states:
    G.add_node((a, b, e))
    for x in one.get(a, []):
        t = (x, e, mul(b, e))
        if t in S_: G.add_edge((a, b, e), t); kind.setdefault(((a, b, e), t), set()).add("P")
    if a != s and a in two:
        for (a2, b2) in two.get(mul(a, e), []):
            if b2 == s: continue
            t = (a2, b2, mul(b, e))
            if t in S_: G.add_edge((a, b, e), t); kind.setdefault(((a, b, e), t), set()).add("R")
big = [c for c in nx.strongly_connected_components(G) if len(c) > 1]
rloops = [u for u in G.nodes if G.has_edge(u, u) and "R" in kind[(u, u)]]
print(f"chain graph: states {G.number_of_nodes()}, edges {G.number_of_edges()}, nontrivial SCCs {len(big)} "
      f"(sizes {sorted((len(c) for c in big), reverse=True)[:5]}), refill self-loops {len(rloops)}")
rho = lambda st: mul(mul(mul(s, st[0]), st[1]), st[2])
for c in big[:3]:
    print("   SCC rho classes:", sorted(collections.Counter(rho(st) for st in c).items())[:10])
print("   refill self-loops (first 10):", rloops[:10], "rho:", sorted(set(rho(u) for u in rloops)))
