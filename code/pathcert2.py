"""Second refinement of the path-model certificate (leftmost / rightmost Böhm-tree paths).

Path states: N(k) = a node known by its joint class k;  A(b, e) = a node q v created by a tail chain, with [q] = b,
[v] = e (its class is b.e). Chain states (a, b, e) = classes of (p, q, v) for App(S p q, v), graph G_J (Theorem Q10).
Node u = S x / S x y: leftmost child x, rightmost child = last argument (proper subterms: 'dec').
Node u with >= 3 arguments, last call App(H(prefix), e_m): chain from (a0, b0, [e_m]) with s.a0.b0 = [prefix] to a final
state (s, bk, ek); hnf = S v_k (q_k v_k).
  leftmost: k = 0 -> child e_m ('dec', N); k >= 1 -> child q_{k-1} v_{k-1} ('new', A(b_{k-1}, e_{k-1})).
  rightmost: child q_k v_k ('new', A(bk, ek)).
Node A(b, e) = q v: q = S -> S v; q = S x -> S x v (syntactic hnfs); q with >= 2 arguments -> chain from (a0, b0, e) with
s.a0.b0 = b. If no 'new' edge lies inside an SCC of the region ('finite' verdict, hnf exists), every path is finite.
Usage: python pathcert2.py left|right
"""
import sys, collections
import networkx as nx
from verify_model import load

side = sys.argv[1]
P = load("../data/model36_leftpath.txt" if side == "left" else "../data/model19_rightpath.txt")
Mm = load("../data/model35_hn.txt")
sP, sM = P[0].index("S"), Mm[0].index("S")
def mul(x, y): return (int(P[2][x[0], y[0]]), int(Mm[2][x[1], y[1]]))
s = (sP, sM)
J = [s]; seen = {s}; i = 0
while i < len(J):
    a = J[i]; i += 1
    for b in J[:i]:
        for c in (mul(a, b), mul(b, a)):
            if c not in seen: seen.add(c); J.append(c)
hasH = lambda k: Mm[1][k[1]] == 1
inC = lambda k: P[1][k[0]] == 0 and hasH(k)
one = collections.defaultdict(list); two = collections.defaultdict(list)
for x in J:
    one[mul(s, x)].append(x)
    for y in J:
        two[mul(mul(s, x), y)].append((x, y))
twoset = set(two)
# chain graph over joint classes (states whose rho has an hnf)
CG = nx.DiGraph()
states = [(a, b, e) for a in J for b in J for e in J if hasH(mul(mul(mul(s, a), b), e))]
Sset = set(states)
for (a, b, e) in states:
    CG.add_node((a, b, e))
    for x in one.get(a, []):
        t = (x, e, mul(b, e))
        if t in Sset: CG.add_edge((a, b, e), t)
    if a != s and a in twoset:
        for (a2, b2) in two.get(mul(a, e), []):
            if b2 == s: continue
            t = (a2, b2, mul(b, e))
            if t in Sset: CG.add_edge((a, b, e), t)
noself = nx.DiGraph([ed for ed in CG.edges if ed[0] != ed[1]]); noself.add_nodes_from(CG.nodes)
print(f"{side}: joint {len(J)}, chain states {CG.number_of_nodes()}, chain edges {CG.number_of_edges()}, "
      f"acyclic apart from self-loops: {nx.is_directed_acyclic_graph(noself)}", flush=True)
# for each chain state: the set of 'last steps' reachable: (penultimate state, final state) pairs, as ids
final = {st for st in states if st[0] == s}
order = list(reversed(list(nx.topological_sort(noself))))
reach = {}
for st in order:
    r = set()
    if st in final: r.add(("F", st))                         # chain may end here (also as k = 0 if st is a start)
    for t in CG.successors(st):
        if t in final: r.add(("P", st, t))                   # st is the penultimate state, t the final one
        if t != st: r |= reach[t]
    reach[st] = frozenset(r)
PG = nx.DiGraph(); lab = collections.defaultdict(set)
def add(u, v, l):
    PG.add_edge(u, v); lab[(u, v)].add(l)
def node_class(st):
    return st[1] if st[0] == "N" else mul(st[1], st[2])
def computed(src, starts):
    for st0 in starts:
        for r in reach.get(st0, ()):
            if r[0] == "F":
                st = r[1]
                if st != st0: continue                      # an end reached only via edges is covered by 'P' items
                child = ("N", st[2]) if side == "left" else ("A", st[1], st[2])
                kind = "dec" if side == "left" else "new"
            else:
                _, pen, fin = r
                child = ("A", pen[1], pen[2]) if side == "left" else ("A", fin[1], fin[2])
                kind = "new"
            if inC(node_class(child)) or not hasH(node_class(child)):
                if hasH(node_class(child)): add(src, child, kind)
    return
for k in J:
    if not inC(k): continue
    src = ("N", k)
    for x in one.get(k, []):
        if hasH(x): add(src, ("N", x), "dec")
    for (x, y) in two.get(k, []):
        c = x if side == "left" else y
        if hasH(c): add(src, ("N", c), "dec")
    starts = [(a0, b0, e) for pi in twoset if pi != s for e in J if mul(pi, e) == k for (a0, b0) in two[pi]]
    computed(src, [st for st in starts if st in Sset])
for b in J:
    for e in J:
        if not inC(mul(b, e)): continue
        src = ("A", b, e)
        if b == s:
            add(src, ("N", e), "dec") if hasH(e) else None
        if b in one:
            for x in one[b]:
                c = x if side == "left" else e
                if hasH(c): add(src, ("N", c), "dec")
        if b != s and b in twoset:
            computed(src, [st for st in ((a0, b0, e) for (a0, b0) in two[b]) if st in Sset])
comp = {}
for idx_, scc in enumerate(nx.strongly_connected_components(PG)):
    for v in scc: comp[v] = idx_
bad = [(u, v) for (u, v), l in lab.items() if "new" in l and comp[u] == comp[v]]
sizes = sorted(collections.Counter(comp.values()).values(), reverse=True)[:5]
print(f"   path graph: {PG.number_of_nodes()} nodes, {PG.number_of_edges()} edges, largest SCCs {sizes}; "
      f"'new' edges inside SCCs: {len(bad)}")
for e in bad[:10]: print("     ", e, sorted(lab[e]))
