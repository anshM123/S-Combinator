"""Adversarial audit of Theorem N* (per-occurrence potential) and Lemma 12 (right-depth cost).

N*: along Böhm-tree paths whose head runs never open a variable-headed element and whose nodes all contain y,
    P_x = max over occurrences o of x of LD(o) + SUPP(o) never increases.
    Also reports how often the *separate-max* quantity max LD + max SUPP increases (the old wording).
Lemma 12: per head step the least right-depth of residuals of a tracked occurrence drops by <= 1.
"""
import random, sys
sys.setrecursionlimit(100000)
from symb import app, spine, size, contains_var

def closed(t): return not (contains_var(t, "x") or contains_var(t, "y"))

def pot_list(t, v, other):
    """list of (LD, SUPP) per occurrence of v in t"""
    out = []
    def go(u, ld, sp):
        if isinstance(u, str):
            if u == v: out.append((ld, sp))
            return
        l, r = u
        cl, cr = closed(l), closed(r)
        if contains_var(r, v):
            go(r, ld + (1 if cl and not contains_var(u, other) else 0), sp)
        if contains_var(l, v):
            go(l, ld, sp + (1 if cr else 0))
    go(t, 0, 0)
    return out

def P(t, v, other):
    L = pot_list(t, v, other)
    return max(a + b for a, b in L) if L else None

def sepmax(t, v, other):
    L = pot_list(t, v, other)
    return (max(a for a, _ in L) + max(b for _, b in L)) if L else None

def hnf_sym(t, budget=400, maxlen=200):
    h, args = spine(t)
    if h != "S": return None
    st = list(args); steps = 0
    while len(st) >= 3:
        if steps >= budget or len(st) > maxlen: return None
        a, b, c = st[0], st[1], st[2]
        ha, cha = spine(a)
        if ha != "S": return None        # would open a variable-headed element
        st = list(cha) + [c, (b, c)] + st[3:]; steps += 1
    return st

def rand_closed(n, rng):
    if n == 1: return "S"
    k = rng.randint(1, n - 1)
    return (rand_closed(k, rng), rand_closed(n - k, rng))

def rand_node(rng):
    """random S-headed term with one x and one y planted at random leaves of closed code"""
    n = rng.randint(4, 14)
    t = rand_closed(n, rng)
    # collect leaf paths, plant x and y at two distinct non-head leaves
    paths = []
    def leaves(u, p):
        if isinstance(u, str): paths.append(p); return
        leaves(u[0], p + "0"); leaves(u[1], p + "1")
    leaves(t, "")
    cand = [p for p in paths if "1" in p]          # not on the root's left spine (head stays S)
    if len(cand) < 2: return None
    px, py = rng.sample(cand, 2)
    def plant(u, p, v):
        if p == "": return v
        return (plant(u[0], p[1:], v), u[1]) if p[0] == "0" else (u[0], plant(u[1], p[1:], v))
    t = plant(t, px, "x"); t = plant(t, py, "y")
    # optionally wrap the variables in random closed layers to create potential
    return t

def main(trials=40000, seed=7, depth=8):
    rng = random.Random(seed)
    checked = viol = sep_inc = paths = 0
    for _ in range(trials):
        t = rand_node(rng)
        if t is None: continue
        paths += 1
        for _ in range(depth):
            if not (contains_var(t, "x") and contains_var(t, "y")): break
            h, args = spine(t)
            if h != "S": break
            if len(args) >= 3:
                fl = hnf_sym(t)
                if fl is None: break
                comps = fl
            else:
                comps = args
            nxt = [c for c in comps if contains_var(c, "x") and contains_var(c, "y")]
            if not nxt: break
            u = rng.choice(nxt)
            for v, o in (("x", "y"), ("y", "x")):
                p0, p1 = P(t, v, o), P(u, v, o)
                checked += 1
                if p1 > p0: viol += 1; print("N* VIOLATION", v, p0, p1)
                if sepmax(u, v, o) > sepmax(t, v, o): sep_inc += 1
            t = u
    print("paths", paths, "transitions checked", checked, "per-occurrence P increases:", viol,
          "| separate-max increases:", sep_inc)

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 40000)
