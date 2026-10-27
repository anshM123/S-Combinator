"""EM hunt on gadget compositions: random trees of 3..L letters over gadget letters and random small terms; keep
L36 flag-1 terms; walk NODES leftmost nodes; after BURN nodes count pops / jumps / returns (EM violations)."""
import sys, random, time
from dm import *
from classes import cls, LFl, clear_cache
from em_hunt import walk, rand_term
from collections import Counter
G = ["S", "SS", "S(SS)", "S(SS)(SS)", "S(S(SS))(S(SS))", "SS(S(SS)(SS))", "S(SS)(S(S(SS))(S(SS)))", "SSS", "S(SSS)",
     "S(S(SS))", "SS(SS)"]
def letter():
    if random.random() < 0.7: return parse(random.choice(G))
    return rand_term(random.randint(2, 7))
def tree(n):
    if n == 1: return letter()
    k = random.randint(1, n - 1)
    return app(tree(k), tree(n - k))
seed, N, maxl, nodes, burn = [int(x) for x in sys.argv[1:6]]
random.seed(seed); t0 = time.time(); tot = Counter(); nw = 0; viol = []; nf1 = 0
for it in range(N):
    m = mark()
    t = tree(random.randint(2, maxl))
    c = cls(t)
    if LFl[c[0]] == 1:
        nf1 += 1
        ty = walk(t, nodes, burn)
        if ty is not None:
            nw += 1; tot.update(ty)
            if (ty["pop"] or ty["jump"] or ty["return"]) and len(viol) < 10: viol.append((show(t)[:120], dict(ty)))
    truncate(m); clear_cache(m)
print("seed", seed, "flag-1 terms", nf1, "walks completing", nodes, "nodes:", nw, "steps after burn-in:", dict(tot), round(time.time() - t0), "s")
print("walks with pops/jumps/returns after burn-in:", viol)
