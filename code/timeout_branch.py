"""Timeout branches (main agent): for every normalising S-term D <= NMAX leaves (delay = passes to normal form) and each
of its parallel states D_t (t = 0..delay), run the parallel head machine from [D_t, c1, c2, r1..r4] (atoms) until an
atom-headed element is at the front; record which atom it is. A timeout branch: the selected continuation changes
between early and late states."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import trees, show
import hc
from parallel_eval import step_fn
NMAX, CAP = int(sys.argv[1]), int(sys.argv[2])
P = step_fn()
NAMES = {-1: "c1", -2: "c2", -3: "r1", -4: "r2", -5: "r3", -6: "r4"}
def select(Dt):
    lst = [Dt, -1, -2, -3, -4, -5, -6]
    for n in range(200):
        a = lst[0]; ch, h = hc.spine(a)
        if h != 0: return NAMES.get(h, "?"), n
        if len(lst) < 3: return "hnf", n
        lst = ch + [lst[2], hc.app(lst[1], lst[2])] + [P(e) for e in lst[3:]]
    return "long", None
found = []
for n in range(1, NMAX + 1):
    for tt in trees(n):
        t = hc.from_tuple(tt); states = [t]; start = len(hc.L); ok = False
        for k in range(CAP):
            u = P(t)
            if u == t: ok = True; break
            t = u; states.append(t)
            if len(hc.L) - start > 100000: break
        if not ok or len(states) < 2: continue
        sel = [select(s)[0] for s in states]
        if len(set(sel)) > 1 and all(x in ("c1", "c2") for x in sel):
            # a clean threshold: one switch from one continuation to the other
            switches = sum(1 for a, b in zip(sel, sel[1:]) if a != b)
            found.append((switches, len(states) - 1, show(tt), sel))
found.sort()
print(f"timeout branches found: {len(found)}")
for sw, D, src, sel in found[:20]:
    print(f"  delay {D}, switches {sw}: {src}: selected per state {sel}")
