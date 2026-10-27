"""Random check of Theorem OT (ordered data cannot drive a proper transfer).
G[b] random closed 1-hole context; b, x, y, r opaque.  Run the generic machine from [G[b], x, y, r] step by step and
check at every step:  (bad pair) some b-containing element lies above an element that is a proper pure-y term
(d1.(d2.(...(dm.y))), m >= 1, all d closed).  The theorem says: if G[b] is ORDERED w.r.t. b (every S-headed
b-containing subterm has spine (b-free)* ++ (b-containing)*), no bad pair ever occurs.  We also count bad pairs for
unordered contexts (they do occur, e.g. S(S b) c)."""
import sys, random
import hm
B = hm.atom("b"); X = hm.atom("x"); Y = hm.atom("y"); R = hm.atom("r")
def atoms(t, memo={}):
    if t <= 0: return frozenset([t]) if t < 0 else frozenset()
    r = memo.get(t)
    if r is None:
        r = atoms(hm.L[t]) | atoms(hm.R[t]); memo[t] = r
    return r
def proper_pure_y(t):
    if t == Y: return False
    while t != Y:
        if t <= 0: return False
        l, r = hm.L[t], hm.R[t]
        if atoms(l): return False      # left part must be closed
        t = r
    return True
def ordered(t):
    """every S-headed b-containing subterm has spine (b-free)* ++ (b-containing)*"""
    stack = [t]
    while stack:
        s = stack.pop()
        if s <= 0 or B not in atoms(s): continue
        a, h = hm.spine(s)
        if h == 0:
            seen_b = False
            for x in a:
                if B in atoms(x): seen_b = True
                elif seen_b: return False
        stack.extend(a)
    return True
def rand_term(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return hm.app(rand_term(k), rand_term(n - k))
def rand_ctx(n):
    """random term of n leaves with exactly one leaf replaced by b"""
    t = rand_term(n)
    leaves = []
    def walk(t, path):
        if t <= 0: leaves.append(path); return
        walk(hm.L[t], path + [0]); walk(hm.R[t], path + [1])
    walk(t, [])
    path = random.choice(leaves)
    def repl(t, path):
        if not path: return B
        if path[0] == 0: return hm.app(repl(hm.L[t], path[1:]), hm.R[t])
        return hm.app(hm.L[t], repl(hm.R[t], path[1:]))
    return repl(t, path)
if __name__ == "__main__":
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    stats = {"ord": [0, 0], "unord": [0, 0]}
    examples = []
    M0 = hm.mark()
    for it in range(N):
        n = random.randint(3, 16)
        G = rand_ctx(n)
        if hm.head(G) != 0: hm.truncate(M0); continue
        kind = "ord" if ordered(G) else "unord"
        st = [R, Y, X, G]
        bad = False
        for step in range(400):
            # check bad pair
            seen_b = False
            for e in reversed(st):      # front first
                if B in atoms(e): seen_b = True
                elif seen_b and proper_pure_y(e): bad = True; break
            if bad: break
            if len(st) < 3: break
            if hm.step(st) < 0: break
        stats[kind][0] += 1
        if bad:
            stats[kind][1] += 1
            if kind == "ord" and len(examples) < 5: examples.append(hm.show(G))
        hm.truncate(M0)
        atoms.__defaults__[0].clear()
    print("runs / runs with a bad pair:", stats)
    print("ordered counterexamples:", examples)
