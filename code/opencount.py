"""How often does a head run open the same original occurrence (through its copies)?

Provenance head machine: a stack element is (base, extra) where base is an occurrence of the original term and
extra are elements appended by b.c; opening (base, extra) exposes ch(base) ++ extra and "opens" base.
For every term with M35 class in F (all have an hnf up to 19 leaves, Theorem B) we record the largest number of
times one occurrence is opened, separately for leaf and application occurrences.
Usage: python opencount.py NMAX [BOTTOM_STEPS]
"""
import sys, collections
from verify_model import load
from symb import trees, show

reps, F, M = load("../data/model35_hn.txt"); s = reps.index("S")
memo = {}
def cl(t):
    if t == "S": return s
    if t in memo: return memo[t]
    r = int(M[cl(t[0]), cl(t[1])]); memo[t] = r; return r

def number(t):
    """occurrence table: kids[id] = spine children ids, leaf[id] = bool; returns (root id, kids, leaf)"""
    kids, leaf = [], []
    def go(u):
        if u == "S":
            kids.append(()); leaf.append(True); return len(kids) - 1
        l = go(u[0]); r = go(u[1])
        kids.append(kids[l] + (r,)); leaf.append(False); return len(kids) - 1
    root = go(t)
    return root, kids, leaf

def run(t, budget):
    root, kids, leaf = number(t)
    stack = [(c, ()) for c in reversed(kids[root])]      # top of stack = end of list
    opens = collections.Counter(); steps = 0
    while len(stack) >= 3 and steps < budget:
        a = stack.pop(); b = stack.pop(); c = stack.pop()
        opens[a[0]] += 1; steps += 1
        stack.append((b[0], b[1] + (c,)))
        stack.append(c)
        for x in reversed([(k, ()) for k in kids[a[0]]] + list(a[1])):
            stack.append(x)
    halted = len(stack) < 3
    mx_leaf = max([v for k, v in opens.items() if leaf[k]], default=0)
    mx_app = max([v for k, v in opens.items() if not leaf[k]], default=0)
    return halted, steps, mx_leaf, mx_app, opens, leaf

if __name__ == "__main__":
  NMAX = int(sys.argv[1]); BSTEPS = int(sys.argv[2]) if len(sys.argv) > 2 else 0
  for n in range(3, NMAX + 1):
    dist_leaf = collections.Counter(); dist_app = collections.Counter(); worst = {}
    bot = collections.Counter(); nf = 0
    for t in trees(n):
        if F[cl(t)]:
            halted, steps, ml, ma, _, _ = run(t, 4 * n + 40)
            assert halted, show(t)
            nf += 1; dist_leaf[ml] += 1; dist_app[ma] += 1
            key = (ml, ma)
            if key not in worst: worst[key] = show(t)
        elif BSTEPS:
            halted, steps, ml, ma, _, _ = run(t, BSTEPS)
            assert not halted
            bot[max(ml, ma)] += 1
    print(f"n={n} F-terms {nf}: max opens of one leaf occ {dict(sorted(dist_leaf.items()))}; "
          f"of one app occ {dict(sorted(dist_app.items()))}", flush=True)
    print("   examples (leaf,app)->term:", {k: worst[k] for k in sorted(worst)}, flush=True)
    if BSTEPS:
        print(f"   bottom terms after {BSTEPS} steps, max opens of one occ: {dict(sorted(bot.items()))}", flush=True)
