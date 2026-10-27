"""Attempt 1: symbolic size-change abstraction of the leftmost Böhm-tree walk inside the joint classes {(14,28),(14,26)}.

Walk machine (exact): configuration K = list of terms (the node is S.K).
  |K| >= 3: head step  K -> open(K[0]) ++ [K[2], K[1].K[2]] ++ K[3:]
  |K| in {1,2}: descend K -> open(K[0])      (the leftmost child)          |K| = 0: halt (leaf S)
Abstract items: ('S',) | ('P', p) slot parameter with a joint class | ('A', l, r) application | ('X', p) a lazy
spine-suffix parameter standing for a list L of terms with pi.L = kappa (classes). Invariant: the class of S applied
to the items before an X item is that X's pi (head steps preserve the class of the prefix by the S-identity).
Opening P(x) gives [X(s -> [x])] with X < x; expanding X(pi -> kappa) gives [] (only if pi = kappa) or
[P(y), X(pi.y -> kappa)] for every class y with kappa reachable from pi.y, with y < X and X' < X.
Sizes: number of nodes of the binary tree; an X counts sum(nodes(e) + 1) over its elements; so opening and expanding
are strictly decreasing. Composites deeper than DMAX and configurations longer than LMAX are folded into fresh
parameters without size relations (sound).
Size-change graphs: arcs (old parameter -> new parameter, strict?). Test: every idempotent closure graph of a cycle
through a descend step, inside the component, has a strict self-arc (Lee-Jones-Ben-Amram).
Usage: python sct_leftmost.py DMAX LMAX MAXSTATES
"""
import sys, collections, itertools
from verify_model import load

DMAX, LMAX, MAXSTATES = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
L36 = load("../data/model36_leftpath.txt"); M35 = load("../data/model35_hn.txt")
sL, sM = L36[0].index("S"), M35[0].index("S")
def jmul(x, y): return (int(L36[2][x[0], y[0]]), int(M35[2][x[1], y[1]]))
s = (sL, sM)
J = [s]; seen = {s}; i = 0
while i < len(J):
    a = J[i]; i += 1
    for b in J[:i]:
        for c in (jmul(a, b), jmul(b, a)):
            if c not in seen: seen.add(c); J.append(c)
idx = {c: k for k, c in enumerate(J)}; n = len(J)
T = [[idx[jmul(J[a], J[b])] for b in range(n)] for a in range(n)]
S0 = idx[s]
COMP = {idx[(14, 28)], idx[(14, 26)]}
MF = [bool(M35[1][J[k][1]]) for k in range(n)]
# reachability by right multiplication (including zero steps)
reach = [[False] * n for _ in range(n)]
for a in range(n):
    st = [a]; reach[a][a] = True
    while st:
        u = st.pop()
        for b in range(n):
            v = T[u][b]
            if not reach[a][v]: reach[a][v] = True; st.append(v)

def icls(it, desc):
    if it[0] == "S": return S0
    if it[0] == "P": return desc[it[1]][1]
    if it[0] == "A": return T[icls(it[1], desc)][icls(it[2], desc)]
    raise ValueError
def depth(it):
    return 1 + max(depth(it[1]), depth(it[2])) if it[0] == "A" else 0

class Ctx:
    """mutable construction context for one transition"""
    def __init__(self, desc):
        self.desc = dict(desc); self.rel = {}; self.nxt = max(desc, default=-1) + 1
    def new(self, d, parents):
        p = self.nxt; self.nxt += 1; self.desc[p] = d
        r = {}
        for (q, strict) in parents:                     # transitive closure to OLD parameters
            for (o, st2) in (self.rel[q].items() if q in self.rel else [(q, False)]):
                r[o] = r.get(o, False) or strict or st2
        self.rel[p] = r
        return p

def open_item(it, ctx):
    if it[0] == "S": return []
    if it[0] == "P":
        x = it[1]
        return [("X", ctx.new(("X", S0, ctx.desc[x][1]), [(x, True)]))]
    if it[0] == "A":
        return open_item(it[1], ctx) + [it[2]]
    raise ValueError(it)

def successors(K, desc):
    """returns list of (newK, ctx, kind) with kind in {'head', 'desc', 'halt'}"""
    out = []
    work = [(list(K), Ctx(desc))]
    while work:
        K, ctx = work.pop()
        cnt = 0; xi = None
        for i, it in enumerate(K):
            if it[0] == "X": xi = i; break
            cnt += 1
            if cnt == 3: break
        if xi is not None:
            p = K[xi][1]; _, pi, ka = ctx.desc[p]
            if pi == ka:
                c2 = Ctx(ctx.desc); c2.rel = dict(ctx.rel); c2.nxt = ctx.nxt
                work.append((K[:xi] + K[xi + 1:], c2))
            for y in range(n):
                py = T[pi][y]
                if not reach[py][ka]: continue
                c2 = Ctx(ctx.desc); c2.rel = {k: dict(v) for k, v in ctx.rel.items()}; c2.nxt = ctx.nxt
                a = c2.new(("P", y), [(p, True)]); b = c2.new(("X", py, ka), [(p, True)])
                work.append((K[:xi] + [("P", a), ("X", b)] + K[xi + 1:], c2))
            continue
        if cnt >= 3:
            a, b, c = K[0], K[1], K[2]
            newK = open_item(a, ctx) + [c, ("A", b, c)] + K[3:]
            out.append((newK, ctx, "head"))
        elif len(K) == 0:
            out.append(([], ctx, "halt"))
        else:
            out.append((open_item(K[0], ctx), ctx, "desc"))
    return out

def run_class(K, desc):
    c = S0
    for it in K:
        if it[0] == "X":
            _, pi, ka = desc[it[1]]
            if c != pi: return None
            c = ka
        else:
            c = T[c][icls(it, desc)]
    return c

def fold(K, ctx):
    """depth / length folding into fresh parameters without size relations"""
    def f(it):
        if it[0] == "A":
            if depth(it) > DMAX:
                return ("P", ctx.new(("P", icls(it, ctx.desc)), []))
            return ("A", f(it[1]), f(it[2]))
        return it
    K = [f(it) for it in K]
    if len(K) > LMAX:
        head, tail = K[:LMAX - 1], K[LMAX - 1:]
        c = S0
        for it in head:
            if it[0] == "X": c = ctx.desc[it[1]][2]
            else: c = T[c][icls(it, ctx.desc)]
        pi = c
        for it in tail:
            if it[0] == "X": c = ctx.desc[it[1]][2]
            else: c = T[c][icls(it, ctx.desc)]
        K = head + [("X", ctx.new(("X", pi, c), []))]
    return K

def canon(K, desc):
    order = []
    def walk(it):
        if it[0] in ("P", "X"):
            if it[1] not in order: order.append(it[1])
        elif it[0] == "A":
            walk(it[1]); walk(it[2])
    for it in K: walk(it)
    ren = {p: k for k, p in enumerate(order)}
    def rn(it):
        if it[0] in ("P", "X"): return (it[0], ren[it[1]])
        if it[0] == "A": return ("A", rn(it[1]), rn(it[2]))
        return it
    key = (tuple(rn(it) for it in K), tuple(desc[p] for p in order))
    return key, ren

def explore():
    init = []
    for k in COMP:
        desc = {0: ("X", S0, k)}
        key, _ = canon([("X", 0)], desc)
        init.append(key)
    states = {}; edges = []; q = list(init)
    for key in init: states[key] = len(states)
    exits = collections.Counter()
    while q:
        key = q.pop()
        if len(states) > MAXSTATES: return states, edges, exits, False
        Kc, descs = key
        desc = {k: d for k, d in enumerate(descs)}
        nodecls = run_class(list(Kc), desc)
        for newK, ctx, kind in successors(list(Kc), desc):
            if kind == "halt": exits["halt"] += 1; continue
            newK = fold(newK, ctx)
            ncls = run_class(newK, ctx.desc)
            if ncls is None: exits["inconsistent"] += 1; continue
            if kind == "desc" and (ncls not in COMP or not MF[ncls]):
                exits["leave/bottom"] += 1; continue
            nkey, ren = canon(newK, ctx.desc)
            arcs = []
            for p, k2 in ren.items():
                if p in desc and p in Kc_params(Kc):
                    arcs.append((p, k2, False))
                elif p in ctx.rel:
                    for o, strict in ctx.rel[p].items():
                        if o in desc: arcs.append((o, k2, strict))
            if nkey not in states:
                states[nkey] = len(states); q.append(nkey)
            edges.append((states[key], states[nkey], frozenset(arcs), kind == "desc"))
    return states, edges, exits, True

_pc = {}
def Kc_params(Kc):
    r = _pc.get(Kc)
    if r is None:
        r = set()
        def walk(it):
            if it[0] in ("P", "X"): r.add(it[1])
            elif it[0] == "A": walk(it[1]); walk(it[2])
        for it in Kc: walk(it)
        _pc[Kc] = r
    return r

def compose(g1, g2):
    best = {}
    for (a, b, s1) in g1:
        for (c, d, s2) in g2:
            if b == c:
                k = (a, d); best[k] = best.get(k, False) or s1 or s2
    return frozenset((a, d, st) for (a, d), st in best.items())

def sct(nstates, edges):
    import networkx as nx
    G = nx.DiGraph(); G.add_nodes_from(range(nstates))
    for (u, v, g, d) in edges: G.add_edge(u, v)
    comp = {}
    for ci, sc in enumerate(nx.strongly_connected_components(G)):
        for v in sc: comp[v] = ci
    out = collections.defaultdict(set)
    for (u, v, g, d) in edges:
        if comp[u] == comp[v]: out[u].add((v, g, d))
    closure = set(); work = []
    for u in out:
        for (v, g, d) in out[u]:
            t = (u, v, g, d)
            if t not in closure: closure.add(t); work.append(t)
    by_src = collections.defaultdict(set)
    for t in closure: by_src[t[0]].add(t)
    while work:
        if len(closure) > 3_000_000: return None, len(closure)
        (u, v, g, d) = work.pop()
        for (w, g2, d2) in out[v]:
            t = (u, w, compose(g, g2), d or d2)
            if t not in closure:
                closure.add(t); by_src[u].add(t); work.append(t)
    bad = []
    for (u, v, g, d) in closure:
        if u == v and d and compose(g, g) == g and not any(a == b and st for (a, b, st) in g):
            bad.append((u, g))
    return bad, len(closure)

if __name__ == "__main__":
    states, edges, exits, complete = explore()
    print(f"abstract states {len(states)} (complete: {complete}), transitions {len(edges)}, "
          f"descend transitions {sum(1 for e in edges if e[3])}, exits {dict(exits)}", flush=True)
    if complete:
        bad, ncl = sct(len(states), edges)
        if bad is None:
            print(f"closure too large ({ncl})")
        else:
            print(f"closure size {ncl}; idempotent descend cycles without a strict self-arc: {len(bad)}")
            inv = {v: k for k, v in states.items()}
            for (u, g) in bad[:3]:
                print("   state:", inv[u]); print("   graph:", sorted(g))
