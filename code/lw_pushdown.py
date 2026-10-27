"""Pushdown abstraction of leftmost Böhm-tree walks (main agent, 2026-10-27). EXPERIMENT, not yet a proof.
Concrete facts used (Theorem Q10's big-step equations): for a node u with >= 3 arguments, prefix P and last argument e,
H(P) = S p q and the tail chain App(S p q, v) runs from (p, q, e): END when p = S (hnf S v (q v), leftmost child v);
peel when p = S x: (x, v, q v); refill when p has >= 2 arguments: H(S x y v) = S p' q' with H(p) = S x y, next
(p', q', q v). So the leftmost child is v_k = q_{k-1}·(…(q_0·e)): a stack of chain values over the base e.
Abstraction over the joint model J = L36 x M35: an opaque node T(k) is known by its class; a stack symbol is the class
of a chain value q_i together with the class of the part below it. Steps on the stack top (b, beta) (node = q·rest):
b = s: pop; b = s·z: leave to T(z) (stack discarded); b with >= 2 arguments: H(q) = S a c with s·a·c = b, run the class
chain from (a, c, beta) and push its values (none: pop). Nondeterministic choices cover every class decomposition, so
the abstraction over-approximates every concrete walk (soundness of each rule is the Q10 equations plus Lemma 3).
This script explores configurations with stack height <= HMAX from every flag-0 class and reports strongly connected
components that contain a non-structural step (candidate infinite runs). Usage: python lw_pushdown.py HMAX"""
import sys, collections
sys.setrecursionlimit(100000)
from verify_model import load

Lr, LF, LT = load("../data/model36_leftpath.txt")
Mr, MF, MT = load("../data/model35_hn.txt")
sL, sM = Lr.index("S"), Mr.index("S")
start = (sL, sM)
J = [start]; idx = {start: 0}; i = 0
while i < len(J):
    for a in list(J[: i + 1]):
        for x, y in ((J[i], a), (a, J[i])):
            c = (int(LT[x[0], y[0]]), int(MT[x[1], y[1]]))
            if c not in idx: idx[c] = len(J); J.append(c)
    i += 1
n = len(J); s = 0
mul = [[idx[(int(LT[J[a][0], J[b][0]]), int(MT[J[a][1], J[b][1]]))] for b in range(n)] for a in range(n)]
FM = [bool(MF[J[k][1]]) for k in range(n)]
FLAG = [int(LF[J[k][0]]) for k in range(n)]            # L36 'HN' column = flag (1 = infinite leftmost path)
Sx = collections.defaultdict(list); Sxy = collections.defaultdict(list)
for x in range(n): Sx[mul[s][x]].append(x)
for x in range(n):
    for y in range(n): Sxy[mul[mul[s][x]][y]].append((x, y))
Pre = set(k for k in Sxy)                               # classes of terms with >= 2 arguments
changed = True
while changed:
    changed = False
    for p in list(Pre):
        for e in range(n):
            if mul[p][e] not in Pre: Pre.add(mul[p][e]); changed = True
PreDec = collections.defaultdict(list)
for p in Pre:
    for e in range(n): PreDec[mul[p][e]].append((p, e))

CH = {}
def chains(a, c, beta, depth=0):
    """all (pushed symbols) lists of class chains from state (a, c, beta) to END; symbols are (q-class, class below)"""
    key = (a, c, beta)
    if key in CH: return CH[key]
    CH[key] = []                                         # cycle guard (Theorem Q10: F-class chains are finite)
    out = set()
    if a == s: out.add(())
    for x in Sx.get(a, ()):                              # peel
        for rest in chains(x, beta, mul[c][beta], depth + 1): out.add(((c, beta),) + rest)
    if a != s and a in Pre and FM[a] and FM[mul[a][beta]]:   # refill
        for (a2, c2) in Sxy.get(mul[a][beta], ()):
            if c2 == s: continue
            for rest in chains(a2, c2, mul[c][beta], depth + 1): out.add(((c, beta),) + rest)
    CH[key] = sorted(out)
    return CH[key]

def succ(conf, HMAX):
    """successor configurations with a flag 'struct' (True = structural, size-decreasing step)"""
    kind = conf[0]
    res = []
    if kind == "T":
        k = conf[1]
        if not FM[k] or k == s: return res               # leaf S or node without hnf: walk ends
        for x in Sx.get(k, ()): res.append((("T", x), True))
        for (x, y) in Sxy.get(k, ()): res.append((("T", x), True))
        for (p, e) in PreDec.get(k, ()):
            if not FM[p]: continue
            for (a, c) in Sxy.get(p, ()):
                for pushes in chains(a, c, e):
                    if not pushes: res.append((("T", e), True))
                    elif len(pushes) <= HMAX: res.append((("K", e, tuple(reversed(pushes))), False))
        return res
    # stack configuration: ("K", base, (top, ..., bottom)) ; each symbol (b, beta)
    base, stack = conf[1], conf[2]
    (b, beta), below = stack[0], stack[1:]
    rest = ("K", base, below) if below else ("T", base)
    node = mul[b][beta]
    if not FM[node]: return res
    if b == s: res.append((rest, True))
    for z in Sx.get(b, ()): res.append((("T", z), False))   # leave the stack: z is part of a chain value
    if b in Pre and FM[b]:
        for (a, c) in Sxy.get(b, ()):
            for pushes in chains(a, c, beta):
                if not pushes: res.append((rest, True))
                else:
                    new = tuple(reversed(pushes)) + below
                    if len(new) <= HMAX: res.append((("K", base, new), False))
    return res

if __name__ == "__main__":
    HMAX = int(sys.argv[1])
    init = [("T", k) for k in range(n) if FLAG[k] == 0 and FM[k]]
    seen = set(init); todo = list(init); edges = collections.defaultdict(set)
    while todo:
        c = todo.pop()
        for d, st in succ(c, HMAX):
            if FLAG[d[1] if d[0] == "T" else mul[d[2][0][0]][d[2][0][1]]] != 0: continue   # flag is preserved; skip
            edges[c].add((d, st))
            if d not in seen: seen.add(d); todo.append(d)
    print(f"joint classes {n}; flag-0 start classes {len(init)}; configurations (stack <= {HMAX}): {len(seen)}")
    # SCCs (iterative Tarjan)
    index = {}; low = {}; onst = set(); st = []; comps = []; counter = [0]
    for v0 in seen:
        if v0 in index: continue
        work = [(v0, iter([d for d, _ in edges.get(v0, ())]))]; index[v0] = low[v0] = counter[0]; counter[0] += 1
        st.append(v0); onst.add(v0)
        while work:
            v, it = work[-1]
            nxt = next(it, None)
            if nxt is None:
                work.pop()
                if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == index[v]:
                    comp = []
                    while True:
                        w = st.pop(); onst.discard(w); comp.append(w)
                        if w == v: break
                    comps.append(comp)
            elif nxt not in index:
                index[nxt] = low[nxt] = counter[0]; counter[0] += 1; st.append(nxt); onst.add(nxt)
                work.append((nxt, iter([d for d, _ in edges.get(nxt, ())])))
            elif nxt in onst:
                low[v] = min(low[v], index[nxt])
    bad = []
    for comp in comps:
        cs = set(comp)
        nonstruct = [(v, d) for v in comp for d, stc in edges.get(v, ()) if d in cs and not stc]
        if nonstruct and (len(comp) > 1 or any(d == comp[0] for d, _ in edges.get(comp[0], ()))): bad.append((comp, nonstruct))
    print(f"SCCs with a non-structural step: {len(bad)}")
    for comp, ns in bad[:5]:
        tk = collections.Counter(J[v[1]] if v[0] == "T" else ("K", len(v[2])) for v in comp)
        print(f"   size {len(comp)}; non-structural edges {len(ns)}; e.g. {ns[0][0]} -> {ns[0][1]}")
