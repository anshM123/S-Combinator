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

def state(u):
    args = hc.spine(u)[0]
    return (cls(u), tuple(cls(a) for a in args))

def graph(u, v):
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
    # closure
    closure = set(edges); by_src = collections.defaultdict(set)
    for e in closure: by_src[e[0]].add(e)
    frontier = list(closure)
    while frontier:
        new = []
        for (a, b, g) in frontier:
            for (b2, c, h) in list(by_src.get(b, ())):
                e = (a, c, compose(g, h))
                if e not in closure:
                    closure.add(e); by_src[a].add(e); new.append(e)
            # also prepend: edges ending at a
        for (a, b, g) in list(closure):
            pass
        frontier = new
        if len(closure) > 2_000_000: print("closure too large; stopping"); break
    # second pass to ensure closure on both sides (compose every pair until stable)
    changed = True
    while changed and len(closure) <= 2_000_000:
        changed = False
        for (a, b, g) in list(closure):
            for (b2, c, h) in list(by_src.get(b, ())):
                e = (a, c, compose(g, h))
                if e not in closure: closure.add(e); by_src[a].add(e); changed = True
    bad = [(a, g) for (a, b, g) in closure if a == b and compose(g, g) == g and not any(p == q and l == "<" for (p, q), l in g)]
    print(f"closure size {len(closure)}; idempotent self-loops without a strict self-arc: {len(bad)}")
    for a, g in bad[:8]: print("   state", a[0], len(a[1]), "slots; graph", sorted(g))
