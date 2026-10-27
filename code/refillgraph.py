"""Abstract tail-chain graph over M35 classes: can a refill step lie on a cycle?

Chain state (a, b, beta) = classes of (p, q, v) for the call App(S p q, v); result class rho = s a b beta must be in F.
H(p) has 0 components iff p = S, 1 component iff p = S x syntactically (then a = s.[x]), else 2 components.
  peel   (p = S x):          (a, b, beta) -> (x, beta, b.beta)        for every class x with s.x = a
  refill (p has spine >= 2): (a, b, beta) -> (a', b', b.beta)         for every (a', b') with s.a'.b' = a.beta
                             (a must be the class of some term with spine >= 2, i.e. some s.x.y)
If no refill edge lies inside a strongly connected component, every tail chain has finitely many refills, and
between refills peels descend structurally, so every chain is finite.
"""
import sys, collections
from opencount import F, M, s

n = M.shape[0]
mul = lambda x, y: int(M[x, y])
one = collections.defaultdict(list)          # a -> [x : s.x = a]
two = collections.defaultdict(list)          # c -> [(x, y) : s.x.y = c]
for x in range(n):
    one[mul(s, x)].append(x)
    for y in range(n):
        two[mul(mul(s, x), y)].append((x, y))
two_classes = set(two)

states = [(a, b, be) for a in range(n) for b in range(n) for be in range(n)
          if F[mul(mul(mul(s, a), b), be)]]
idx = {st: i for i, st in enumerate(states)}
edges = collections.defaultdict(set); kind = {}
for (a, b, be) in states:
    src = idx[(a, b, be)]
    for x in one.get(a, []):                                 # peel
        st = (x, be, mul(b, be))
        if st in idx:
            edges[src].add(idx[st]); kind.setdefault((src, idx[st]), set()).add("P")
    if a != s and a in two_classes:                          # refill
        for (a2, b2) in two.get(mul(a, be), []):
            if b2 == s:
                continue                      # after a refill the second component is an application, never S
            st = (a2, b2, mul(b, be))
            if st in idx:
                edges[src].add(idx[st]); kind.setdefault((src, idx[st]), set()).add("R")

# Tarjan SCC (iterative)
index = {}; low = {}; onst = set(); stack = []; comp = {}; c = 0; counter = [0]
for root in range(len(states)):
    if root in index: continue
    work = [(root, iter(edges[root]))]; index[root] = low[root] = counter[0]; counter[0] += 1
    stack.append(root); onst.add(root)
    while work:
        v, it = work[-1]
        nxt = next(it, None)
        if nxt is None:
            work.pop()
            if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                while True:
                    w = stack.pop(); onst.discard(w); comp[w] = c
                    if w == v: break
                c += 1
        elif nxt not in index:
            index[nxt] = low[nxt] = counter[0]; counter[0] += 1
            stack.append(nxt); onst.add(nxt); work.append((nxt, iter(edges[nxt])))
        elif nxt in onst:
            low[v] = min(low[v], index[nxt])

cyc_refill = [(u, v) for (u, v), k in kind.items() if "R" in k and comp[u] == comp[v]]
nedges = sum(len(e) for e in edges.values())
print(f"states {len(states)}, edges {nedges}, SCCs {c}")
print(f"refill edges inside an SCC: {len(cyc_refill)}")
for (u, v) in cyc_refill[:10]:
    print("   ", states[u], "->", states[v])
sizes = collections.Counter(comp.values())
print("largest SCCs:", sorted(sizes.values(), reverse=True)[:5])
