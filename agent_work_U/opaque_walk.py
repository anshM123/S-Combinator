"""Leftmost walks of W.x for closed W and an opaque variable x (DM with atoms): classify how the walk ends:
'S' (leaf), 'var' (reaches an x-headed node: the walk would execute the fuel), 'closed' (x erased: continues as a closed
walk — stopped here), 'bot?' (round budget), 'long' (NODES nodes keeping x, never executing it)."""
import sys
from dm import *
from collections import Counter
NODES = 300
x = atom("x")
def has_x(u):
    st = [u]; seen = set()
    while st:
        a = st.pop()
        if a < 0: return True
        if a == 0 or a in seen: continue
        seen.add(a); st.append(L[a]); st.append(R[a])
    return False
def head_of(u):
    while u > 0: u = L[u]
    return u
def walk(u):
    for j in range(NODES):
        if u == 0: return "S", j
        if head_of(u) < 0: return "var", j
        if not has_x(u): return "closed", j
        args = spine(u)[0]
        if len(args) <= 2: u = args[0]; continue
        st = list(reversed(args)); k = 0
        while len(st) > 2:
            a = st.pop()
            if head_of(a) < 0: return "var", j
            b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(a)[0])); k += 1
            if k > 5000: return "bot?", j
        u = st[-1]
    return "long", NODES
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
stat = Counter(); ex = []
for n in range(2, int(sys.argv[1]) + 1):
    for W in trees(n):
        w, j = walk(app(W, x))
        stat[w] += 1
        if w == "long" and len(ex) < 10: ex.append(show(W))
    print(n, dict(stat), flush=True)
print("long examples:", ex)
