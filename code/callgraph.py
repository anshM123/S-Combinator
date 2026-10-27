"""Abstract call-graph check for the converse of C1 ([t] in F  =>  t has a head normal form).

Big-step head normalisation (PROOF.md, Lemma 2):
  H(S) = S,   H(t1 t2) = App(H(t1), t2)
  App(S, v) = S v,   App(S p, v) = S p v,   App(S p q, v) = App(App(H(p), v), q v)

Calls: H(t) and App(h, v) with h a 2-component hnf.  An infinite head reduction yields an infinite
path in the call tree.  We abstract every call by classes of the finite S-model M:
  H-node  H(a)        : a = [t]                                    (result class a)
  App-node App(e, b)  : e = [h] (h = S p q, so e = s*pi*kappa), b = [v]   (result class e*b)
Edges (all choices consistent with the model are added => over-approximation):
  H(a)      -> H(x)            for every factorisation x*y = a        (non-tail, structural descent)
  H(a)      -> App(x, y)       for every factorisation x*y = a, x two-component
  App(e, b) -> H(pi)           for every decomposition s*pi*kappa = e
  App(e, b) -> App(pi, b)      ...                                     if pi two-component
  App(e, b) -> App(pi*b, kappa*b) ...                                  if pi*b two-component (tail)
Only nodes with result class in F are kept (a diverging call can only sit inside calls whose result
class is in F once the root's class is in F, because bottom is left-absorbing).
H->H edges strictly decrease the term, so a concrete infinite path visits App nodes infinitely often.
Hence: if no cycle of the abstract graph passes through an App node, every term with class in F has
a head normal form.
"""
import sys
from verify_model import load

def main(path):
    reps, hn, tab = load(path)
    m = len(reps); s = reps.index("S")
    F = [bool(hn[i]) for i in range(m)]
    two = {}          # e -> list of (pi, kappa) with s*pi*kappa = e
    for pi in range(m):
        for ka in range(m):
            two.setdefault(int(tab[tab[s, pi], ka]), []).append((pi, ka))
    fact = {}         # a -> list of (x, y) with x*y = a
    for x in range(m):
        for y in range(m):
            fact.setdefault(int(tab[x, y]), []).append((x, y))
    nodes = []
    for a in range(m):
        if F[a]:
            nodes.append(("H", a))
    for e in two:
        for b in range(m):
            if F[int(tab[e, b])]:
                nodes.append(("A", e, b))
    nodeset = set(nodes)
    adj = {u: set() for u in nodes}
    for u in nodes:
        if u[0] == "H":
            a = u[1]
            for (x, y) in fact.get(a, []):
                if ("H", x) in nodeset: adj[u].add(("H", x))
                if x in two and ("A", x, y) in nodeset: adj[u].add(("A", x, y))
        else:
            _, e, b = u
            for (pi, ka) in two[e]:
                if ("H", pi) in nodeset: adj[u].add(("H", pi))
                if pi in two and ("A", pi, b) in nodeset: adj[u].add(("A", pi, b))
                w = int(tab[pi, b]); vb = int(tab[ka, b])
                if w in two and ("A", w, vb) in nodeset: adj[u].add(("A", w, vb))
    # strongly connected components (Tarjan, iterative)
    index = {}; low = {}; onst = set(); st = []; sccs = []; idx = [0]
    for root in nodes:
        if root in index: continue
        work = [(root, iter(adj[root]))]
        index[root] = low[root] = idx[0]; idx[0] += 1; st.append(root); onst.add(root)
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = idx[0]; idx[0] += 1; st.append(w); onst.add(w)
                    work.append((w, iter(adj[w]))); advanced = True; break
                elif w in onst:
                    low[v] = min(low[v], index[w])
            if advanced: continue
            work.pop()
            if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = st.pop(); onst.discard(w); comp.append(w)
                    if w == v: break
                sccs.append(comp)
    bad = []
    for comp in sccs:
        cyclic = len(comp) > 1 or comp[0] in adj[comp[0]]
        if cyclic and any(u[0] == "A" for u in comp):
            bad.append(comp)
    hcyc = [c for c in sccs if (len(c) > 1 or c[0] in adj[c[0]]) and all(u[0] == "H" for u in c)]
    print(f"nodes={len(nodes)} edges={sum(len(v) for v in adj.values())} SCCs={len(sccs)}")
    print(f"cyclic SCCs through an App node: {len(bad)}; H-only cyclic SCCs (harmless): {len(hcyc)}")
    for comp in bad[:5]:
        print("  bad SCC size", len(comp), "e.g.", sorted(comp)[:12])
    return bad

if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "../data/model35_hn.txt")
