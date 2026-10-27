"""Transfer graph between 1-hole contexts.  Edge G -> H when the generic run of [G[b], x, y | r] (b, x, y, r opaque)
gets stuck with a b-headed front (b itself or b.w...) whose activation input v (the element at position 3 if the
front is bare b, else the front's first extra arg... we use: the third list element) equals H[y] for a context H
in which y occurs exactly once and x, b, r do not occur.  A Church-style two-counter transfer loop needs a cycle.
Start from the contexts G = c.[] for closed c (these are what F = S(S[])c produces) and from all small contexts."""
import sys, collections
import hm
Bh = hm.atom("b"); X = hm.atom("x"); Y = hm.atom("y"); Rr = hm.atom("r")
HOLE = hm.atom("#")
def subst(t, at, val, memo=None):
    if memo is None: memo = {}
    if t == at: return val
    if t <= 0: return t
    r = memo.get(t)
    if r is None:
        r = hm.app(subst(hm.L[t], at, val, memo), subst(hm.R[t], at, val, memo)); memo[t] = r
    return r
def atoms(t):
    s = collections.Counter(); st = [t]
    while st:
        i = st.pop()
        if i < 0: s[i] += 1
        elif i > 0: st.append(hm.L[i]); st.append(hm.R[i])
    return s
def edge(G, budget=3000):
    """G: context with HOLE.  returns (kind, H) where H is a context with HOLE, or None"""
    Gb = subst(G, HOLE, Bh)
    if hm.head(Gb) != 0: return None
    st = [Rr, Y, X, Gb]
    s, k = hm.run(st, budget)
    if s != "stuck": return None
    f = st[-1]
    if hm.head(f) != Bh: return None
    fa, _ = hm.spine(f)
    # v-input of b's activation: if b has no extra args, inputs are (st[-2], st[-3]) -> v = st[-3];
    # if b has extra args w1.., b's own spine is unknown, so the 'next activation' is of b's first arg ... we only
    # accept a bare b front (clean pred activation)
    if fa: return ("junkfront", None)
    if len(st) < 3: return None
    v = st[-3]
    a = atoms(v)
    if a == collections.Counter({Y: 1}):
        return ("clean", subst(v, Y, HOLE))
    return ("dirty", None)
_ctx = {}
def contexts(n):
    if n in _ctx: return _ctx[n]
    out = []
    if n == 1: out = [HOLE]
    else:
        for k in range(1, n):
            for l in contexts(k):
                for rr in hm.trees(n - k): out.append(hm.app(l, rr))
            for l in hm.trees(k):
                for rr in contexts(n - k): out.append(hm.app(l, rr))
    _ctx[n] = out
    return out
if __name__ == "__main__":
    smax = int(sys.argv[1])
    edges = {}; stats = collections.Counter()
    for n in range(2, smax + 1):
        for G in contexts(n):
            e = edge(G)
            if e is None: stats["none"] += 1; continue
            stats[e[0]] += 1
            if e[0] == "clean": edges[G] = e[1]
    print(stats, "clean edges:", len(edges))
    # follow chains
    for G, H in list(edges.items()):
        chain = [G]; cur = H; seen = {G}
        while True:
            chain.append(cur)
            if cur in seen: break
            seen.add(cur)
            if cur in edges: cur = edges[cur]
            else:
                e = edge(cur)
                if e and e[0] == "clean": edges[cur] = e[1]; cur = e[1]
                else: break
        if len(chain) >= 3 or chain[-1] in chain[:-1]:
            cyc = chain[-1] in chain[:-1]
            if cyc or len(chain) >= 4:
                print(("CYCLE " if cyc else "chain ") + " -> ".join(hm.show(c) for c in chain))

def explain(G):
    Gb = subst(G, HOLE, Bh)
    st = [Rr, Y, X, Gb]
    s, k = hm.run(st, 3000)
    return s, k, hm.show_list(st)
