"""Refined abstract analysis of App tail chains (obligation (A) of C1).

Concrete chain: h_i = S p_i q_i, argument v_i; next v_{i+1} = q_i v_i and (p_{i+1}, q_{i+1}) = comps of hnf(p_i v_i).
Abstract state: (shape(p), pi, kappa, beta) where pi=[p], kappa=[q], beta=[v] and
  shape(p) = ('S',)                         p = S                  -> chain ends
           = ('S1', x)                      p = S x   (hnf)        -> PEEL:   p' = x (proper subterm)
           = ('S2', x, y)                   p = S x y (hnf)        -> REFILL: nested App(S x y, v)
           = ('N',)                         p not an hnf           -> REFILL: nested H(p) first
For a fresh first component of class c we branch over every shape consistent with c:
  'S' if c == s;  ('S1', x) if s*x == c;  ('S2', x, y) if s*x*y == c;  ('N',) always (non-hnf terms of class c
  exist for every c? -- we over-approximate and allow it).
Result class rho = pi*beta*(kappa*beta) must lie in F and is constant along the chain.
If no cycle contains a REFILL edge then every chain has finitely many refills and then only peels,
which strictly decrease p, so the chain is finite.
"""
import sys
from verify_model import load

def main(path, allow_N=True):
    reps, hn, tab = load(path)
    m = len(reps); s = reps.index("S")
    F = [bool(x) for x in hn]
    mul = lambda a, b: int(tab[a, b])
    two = {}
    for x in range(m):
        for y in range(m):
            two.setdefault(mul(mul(s, x), y), []).append((x, y))
    one = {}
    for x in range(m):
        one.setdefault(mul(s, x), []).append(x)

    def shapes(c):
        out = []
        if c == s: out.append(("S",))
        for x in one.get(c, []): out.append(("S1", x))
        for (x, y) in two.get(c, []): out.append(("S2", x, y))
        if allow_N: out.append(("N",))
        return out

    def comps(c):  # decompositions of a class as a 2-component hnf
        return two.get(c, [])

    states = set(); edges = {}
    frontier = []
    for e in range(m):
        for (pi, ka) in comps(e):
            for b in range(m):
                if not F[mul(e, b)]: continue
                for sh in shapes(pi):
                    st = (sh, pi, ka, b)
                    if st not in states:
                        states.add(st); frontier.append(st)
    while frontier:
        st = frontier.pop()
        sh, pi, ka, b = st
        out = []
        rho = mul(mul(pi, b), mul(ka, b))
        nb = mul(ka, b)                 # class of q v
        if sh[0] == "S":
            pass                         # chain ends
        elif sh[0] == "S1":
            x = sh[1]
            # h' = S x v : pi' = [x], kappa' = beta
            for sh2 in shapes(x):
                out.append(("PEEL", (sh2, x, b, nb)))
        else:
            # REFILL: w = hnf(p v) has class pi*b; any 2-component decomposition
            w = mul(pi, b)
            for (p2, q2) in comps(w):
                for sh2 in shapes(p2):
                    out.append(("REFILL", (sh2, p2, q2, nb)))
        edges[st] = []
        for lab, st2 in out:
            if not F[mul(mul(st2[1], st2[3]), mul(st2[2], st2[3]))]:
                continue
            assert mul(mul(st2[1], st2[3]), mul(st2[2], st2[3])) == rho
            edges[st].append((lab, st2))
            if st2 not in states:
                states.add(st2); frontier.append(st2)
    # SCC
    sys.setrecursionlimit(1000000)
    idx = {}; low = {}; onst = set(); stk = []; comp_of = {}; ncomp = [0]; counter = [0]
    def strong(v):
        idx[v] = low[v] = counter[0]; counter[0] += 1; stk.append(v); onst.add(v)
        for _, w in edges.get(v, []):
            if w not in idx:
                strong(w); low[v] = min(low[v], low[w])
            elif w in onst:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            while True:
                w = stk.pop(); onst.discard(w); comp_of[w] = ncomp[0]
                if w == v: break
            ncomp[0] += 1
    for v in list(states):
        if v not in idx: strong(v)
    bad = [(v, lab, w) for v in states for lab, w in edges.get(v, []) if lab == "REFILL" and comp_of[v] == comp_of[w]]
    print(f"allow_N={allow_N}: states={len(states)} edges={sum(len(e) for e in edges.values())} "
          f"REFILL edges inside a cycle: {len(bad)}")
    for v, lab, w in bad[:8]:
        print("   ", v, "->", w)
    return bad

if __name__ == "__main__":
    p = sys.argv[1] if len(sys.argv) > 1 else "../data/model35_hn.txt"
    main(p, allow_N=True)
    main(p, allow_N=False)
