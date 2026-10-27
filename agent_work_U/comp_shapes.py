"""Census of computed nodes in the component {(14,28),(14,26)}: arity and the joint classes of the spine arguments."""
import sys
from dm import *
from classes import cls, COMPONENT
from collections import Counter
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
shapes = Counter(); ex = {}
nmax = int(sys.argv[1])
for n in range(3, nmax + 1):
    for t in trees(n):
        if cls(t) not in COMPONENT: continue
        u = t
        for j in range(60):
            args, h = spine(u)
            if len(args) == 0: break
            if len(args) <= 2: u = args[0]; continue
            cu = cls(u)
            if cu in COMPONENT:
                key = (cu, tuple(cls(a) for a in args))
                shapes[key] += 1
                if key not in ex: ex[key] = show(u, maxlen=100)
            st = list(reversed(args)); k = 0
            while len(st) > 2 and k < 3000:
                a = st.pop(); b = st.pop(); c = st.pop()
                st.append(app(b, c)); st.append(c); st.extend(reversed(spine(a)[0])); k += 1
            if len(st) > 2: break
            u = st[-1]
print(len(shapes), "distinct shapes")
for key, v in shapes.most_common(60): print(v, key, ex[key])
