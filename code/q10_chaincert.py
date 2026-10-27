"""Certificate check for BEKW Question 10 via tail chains (PROOF.md, Theorem Q10).

Independent re-implementation of the abstract tail-chain graph (refillgraph.py) with three checks:
 (1) Lemma 15: no product of M35 equals the class s of S;
 (2) the graph on states (a, b, beta) with s.a.b.beta in F, peel edges (a = s.x) -> (x, beta, b.beta) and refill edges
     (a a class s.x.y, a != s) -> (a', b', b.beta) with s.a'.b' = a.beta and b' != s, is acyclic apart from self-loops,
     and has no refill self-loop  [networkx SCCs];
 (3) every transition of every tail chain of every M35-F term with <= NMAX leaves is an edge of the graph with the
     right kind (validates the modelling against concrete runs).
Usage: python q10_chaincert.py NMAX
"""
import sys, collections
import networkx as nx
from opencount import F, M, s, cl
from symb import trees, show, spine

n = M.shape[0]
mul = lambda x, y: int(M[x, y])
assert all(mul(x, y) != s for x in range(n) for y in range(n)), "Lemma 15 fails"
print("(1) no product equals s: OK")

one = collections.defaultdict(list); two = collections.defaultdict(list)
for x in range(n):
    one[mul(s, x)].append(x)
    for y in range(n):
        two[mul(mul(s, x), y)].append((x, y))

G = nx.DiGraph(); kinds = collections.defaultdict(set)
states = [(a, b, be) for a in range(n) for b in range(n) for be in range(n) if F[mul(mul(mul(s, a), b), be)]]
S_ = set(states)
for (a, b, be) in states:
    G.add_node((a, b, be))
    for x in one.get(a, []):
        t = (x, be, mul(b, be))
        if t in S_:
            G.add_edge((a, b, be), t); kinds[((a, b, be), t)].add("P")
    if a != s and a in two:
        for (a2, b2) in two.get(mul(a, be), []):
            if b2 == s:
                continue                      # refill targets have an application as second component
            t = (a2, b2, mul(b, be))
            if t in S_:
                G.add_edge((a, b, be), t); kinds[((a, b, be), t)].add("R")
sccs = list(nx.strongly_connected_components(G))
big = [c for c in sccs if len(c) > 1]
refill_loops = [u for u in G.nodes if G.has_edge(u, u) and "R" in kinds[(u, u)]]
peel_loops = [u for u in G.nodes if G.has_edge(u, u) and "P" in kinds[(u, u)]]
print(f"(2) states {G.number_of_nodes()}, edges {G.number_of_edges()}, SCCs {len(sccs)}, "
      f"non-trivial SCCs {len(big)}, refill self-loops {len(refill_loops)}, peel self-loops {len(peel_loops)}")
print("    acyclic apart from self-loops:", nx.is_directed_acyclic_graph(nx.DiGraph([e for e in G.edges if e[0] != e[1]])))

# (3) validate against concrete tail chains
sys.setrecursionlimit(1000000)
bad = 0; checked = 0
def H(t):
    if t == "S": return ()
    return App(H(t[0]), t[1])
def App(h, v):
    global bad, checked
    if len(h) < 2: return h + (v,)
    while len(h) == 2:
        p, q = h
        hp = H(p)
        h2 = App(hp, v)
        if len(h2) == 2:                      # the chain continues: check the abstract edge
            u = (cl(p), cl(q), cl(v)); w = (cl(h2[0]), cl(h2[1]), cl((q, v)))
            k = {0: None, 1: "P", 2: "R"}[len(hp)]
            checked += 1
            if not (G.has_edge(u, w) and k in kinds[(u, w)]):
                bad += 1
                if bad <= 5: print("    MISSING edge", u, w, k)
        h, v = h2, (q, v)
    return h + (v,)
NMAX = int(sys.argv[1])
for m in range(1, NMAX + 1):
    for t in trees(m):
        if F[cl(t)]:
            H(t)
print(f"(3) concrete chain transitions checked {checked}, not in graph {bad}")
