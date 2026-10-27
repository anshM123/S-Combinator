"""Size-change experiment on leftmost Böhm-tree walks in the resisting component {(14,28), (14,26)} (main agent, 2026-10-26).
EMPIRICAL abstraction (not a proof): a walk step u -> u' is abstracted by the states (joint class of u, joint classes of
its arguments) and a size-change graph between argument slots: arc p -> q is '=' if arg_q(u') equals arg_p(u), and '<'
if arg_q(u') is a proper subterm of arg_p(u) (also when u' itself is a proper subterm of arg_p(u): then every slot of u'
gets '<' from p). The Lee-Jones-Ben-Amram closure is computed over the observed (state, state, graph) triples; an
idempotent self-loop graph without a strict self-arc is reported (a candidate non-terminating pattern of the
abstraction). Usage: python lw_sct.py NMAX [RANDOM_N RANDOM_LEAVES_MAX]"""
import sys, random, collections
sys.setrecursionlimit(1000000)
import hc
from li_explore import terms
from lw_anatomy import cls, walk

SUB = {}
def subterms(i):
    """set of proper subterm ids of i (memoised)"""
    r = SUB.get(i)
    if r is None:
        if i == 0: r = frozenset()
        else:
            l, rr = hc.L[i], hc.R[i]
            r = frozenset({l, rr}) | subterms(l) | subterms(rr)
        SUB[i] = r
    return r

import os
MODE = os.environ.get("SCT_MODE", "class")
def state(u):
    a = hc.spine(u)[0]; m = len(a)
    if MODE == "class": return (cls(u), 0)
    if MODE == "nargs": return (cls(u), min(m, 8))
    if MODE == "firstlast": return (cls(u), (cls(a[0]) if m else None, cls(a[-1]) if m else None))
    if MODE == "all3": return (cls(u), (min(m, 8), cls(a[0]) if m else None, cls(a[-1]) if m else None))
    if MODE.startswith("ends"):
        K = int(MODE[4:])
        return (cls(u), (min(m, 2 * K + 1), tuple(cls(x) for x in a[:K]), tuple(cls(x) for x in a[-K:]) if m > K else ()))
    raise ValueError(MODE)

def params(u):
    """fixed parameter slots: node, first three arguments, last two arguments (None when absent)"""
    a = list(hc.spine(u)[0]); m = len(a)
    return [u, a[0] if m > 0 else None, a[1] if m > 1 else None, a[2] if m > 2 else None,
            a[-1] if m > 0 else None, a[-2] if m > 1 else None]

SZ = {0: 1}
def size(i):
    r = SZ.get(i)
    if r is None: r = SZ[i] = size(hc.L[i]) + size(hc.R[i])
    return r

def graph(u, v):
    """size-based arcs between all slots (slot -1 = the whole node): sound for SCT (size is well-founded)"""
    au, av = params(u), params(v)
    arcs = {}
    for p, x in enumerate(au):
        if x is None: continue
        for q, y in enumerate(av):
            if y is None: continue
            if size(y) < size(x): arcs[(p - 1, q - 1)] = "<"
            elif size(y) == size(x): arcs[(p - 1, q - 1)] = "="
    return frozenset(arcs.items())

def graph_subterm(u, v):
    au, av = hc.spine(u)[0], hc.spine(v)[0]
    arcs = {}
    for p, x in enumerate(au):
        sx = subterms(x)
        if v == x or v in sx:                      # v is (a subterm of) slot p: all of v's slots are below x
            for q in range(len(av)): arcs[(p, q)] = "<"
            continue
        for q, y in enumerate(av):
            if y == x: arcs[(p, q)] = arcs.get((p, q), "=")
            elif y in sx: arcs[(p, q)] = "<"
    return frozenset(arcs.items())

def compose(g1, g2):
    out = {}
    d2 = collections.defaultdict(list)
    for (q, r), l in g2: d2[q].append((r, l))
    for (p, q), l1 in g1:
        for r, l2 in d2.get(q, ()):
            l = "<" if "<" in (l1, l2) else "="
            if out.get((p, r)) != "<": out[(p, r)] = l
    return frozenset(out.items())

if __name__ == "__main__":
    NMAX = int(sys.argv[1])
    target = {(14, 28), (14, 26)}
    starts = [t for n in range(3, NMAX + 1) for t in terms(n) if cls(t) in target]
    if len(sys.argv) > 3:
        from irregular_hunt import rand_term
        rng = random.Random(1); want = int(sys.argv[2]); lmax = int(sys.argv[3]); got = 0
        while got < want:
            t = hc.from_tuple(rand_term(rng, rng.randint(NMAX + 1, lmax)))
            if cls(t) in target: starts.append(t); got += 1
    edges = set()
    for t in starts:
        nodes, kinds, end = walk(t)
        for u, v in zip(nodes, nodes[1:]):
            if cls(u) in target and cls(v) in target:
                edges.add((state(u), state(v), graph(u, v)))
    print(f"walk starts: {len(starts)}; abstract edges inside the component: {len(edges)}; "
          f"states: {len({e[0] for e in edges} | {e[1] for e in edges})}", flush=True)
    # closure by worklist: extend every new path graph by one BASE edge (enough for the full composition closure)
    base_by_src = collections.defaultdict(list)
    for (a, b, g) in edges: base_by_src[a].append((b, g))
    closure = set(edges); work = list(edges); CAP = 3_000_000
    while work and len(closure) < CAP:
        a, b, g = work.pop()
        for c, h in base_by_src.get(b, ()):
            e = (a, c, compose(g, h))
            if e not in closure:
                closure.add(e); work.append(e)
    if work: print(f"closure capped at {len(closure)} (not complete)")
    bad = [(a, g) for (a, b, g) in closure if a == b and compose(g, g) == g and not any(p == q and l == "<" for (p, q), l in g)]
    print(f"[{MODE}] states {len({e[0] for e in edges} | {e[1] for e in edges})}; closure size {len(closure)}; idempotent self-loops without a strict self-arc: {len(bad)}")
    for a, g in bad[:3]: print("   state", a, "graph", sorted(g))

    # which slots carry the strict self-arcs of the idempotent self-loops?
    stat = collections.Counter(); only = collections.Counter(); total = 0
    for (a, b, g) in closure:
        if a == b and compose(g, g) == g:
            total += 1
            strict = sorted(p for (p, q), l in g if p == q and l == "<")
            for p in strict: stat[p] += 1
            only[tuple(strict)] += 1
    print(f"idempotent self-loops: {total}; strict self-arc slot counts (slot -1 = whole node): {dict(sorted(stat.items()))}")
    print("most common strict-arc sets:", only.most_common(8))
    node_always = all(any(p == -1 and q == -1 and l == "<" for (p, q), l in g)
                      for (a, b, g) in closure if a == b and compose(g, g) == g)
    print("whole-node size strictly decreases in every idempotent self-loop:", node_always)
