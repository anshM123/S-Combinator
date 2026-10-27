import random, sys
sys.setrecursionlimit(100000)
import audit_pot as A
from symb import contains_var, spine
import fullread as F

def rand_ctx(v, rng):
    """random closed term (2..7 leaves) with one leaf (not the head) replaced by v"""
    while True:
        t = A.rand_closed(rng.randint(2, 7), rng)
        paths = []
        def leaves(u, p):
            if isinstance(u, str): paths.append(p); return
            leaves(u[0], p + "0"); leaves(u[1], p + "1")
        leaves(t, "")
        cand = [p for p in paths if "1" in p]
        if cand: break
    p = rng.choice(cand)
    def plant(u, p):
        if p == "": return v
        return (plant(u[0], p[1:]), u[1]) if p[0] == "0" else (u[0], plant(u[1], p[1:]))
    return plant(t, p)

def deep_var(v, rng):
    t = v
    for _ in range(rng.randint(1, 3)):
        t = rand_ctx(t, rng) if isinstance(t, str) else (lambda c: c)(subst(rand_ctx("@", rng), t))
    return t

def subst(t, val):
    if isinstance(t, str): return val if t == "@" else t
    return (subst(t[0], val), subst(t[1], val))

def node(rng):
    t = A.rand_node(rng)
    if t is None: return None
    return subst2(t, {"x": deep_var("x", rng), "y": deep_var("y", rng)})

def subst2(t, m):
    if isinstance(t, str): return m.get(t, t)
    return (subst2(t[0], m), subst2(t[1], m))

def nstar(trials, seed=11, depth=10):
    rng = random.Random(seed); checked = viol = sep = 0; maxp = 0
    for _ in range(trials):
        t = node(rng)
        if t is None: continue
        for _ in range(depth):
            if not (contains_var(t, "x") and contains_var(t, "y")): break
            h, args = spine(t)
            if h != "S": break
            comps = A.hnf_sym(t) if len(args) >= 3 else args
            if comps is None: break
            nxt = [c for c in comps if contains_var(c, "x") and contains_var(c, "y")]
            if not nxt: break
            u = rng.choice(nxt)
            for v, o in (("x", "y"), ("y", "x")):
                p0, p1 = A.P(t, v, o), A.P(u, v, o); checked += 1; maxp = max(maxp, p0)
                if p1 > p0: viol += 1
                if A.sepmax(u, v, o) > A.sepmax(t, v, o): sep += 1
            t = u
    print("N* (layered variables): transitions", checked, "max P seen", maxp, "P increases", viol, "sep-max increases", sep)

def rightdepth(trials, seed=5):
    rng = random.Random(seed); steps_checked = viol = 0
    for _ in range(trials):
        m = rng.randint(3, 6)
        args = [F.rand_tree(rng.randint(1, 9), rng) for _ in range(m)]
        allnodes = [u for e in args for u in F.nodes(e, [])]
        target = rng.choice(allnodes)
        st = args[:]          # top first
        def mind(lst):
            best = None
            for e in lst:
                stack = [(e, 0)]
                while stack:
                    u, r = stack.pop()
                    if u is target: best = r if best is None else min(best, r)
                    if u.l is not None: stack.append((u.l, r)); stack.append((u.r, r + 1))
            return best
        d = mind(st)
        for _ in range(150):
            if len(st) < 3 or target.mark: break
            a, b, c = st[0], st[1], st[2]
            st = F.open_elem(a) + [c, F.N(b, c, orig=False)] + st[3:]
            if len(st) > 120: break
            d2 = mind(st); steps_checked += 1
            if d is not None and d2 is not None and d2 < d - 1: viol += 1
            d = d2
    print("Lemma 12: head steps checked", steps_checked, "violations (drop > 1)", viol)

if __name__ == "__main__":
    nstar(int(sys.argv[1]) if len(sys.argv) > 1 else 20000)
    rightdepth(int(sys.argv[2]) if len(sys.argv) > 2 else 3000)
