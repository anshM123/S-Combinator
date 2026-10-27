"""What can one countdown LAYER do to the supply? (main agent, frontier research)

For every one-hole closed context L[.] with <= LMAX leaves (the hole counted as a leaf), predecessor p opaque, body B
(concrete SS-nest N_2 over S(SS)(SS), or head-style X_2), fuel S, opaque tape: run the head machine from the front node
L[p]·S^n·B·S and record m if the front element later becomes p·S^m·B·S (the next node, A's predecessor in front).
Classifies each context by its effect n -> m on the supply for n = 0..NMAX: increment (+r), neutral, DECREMENT (n -> n-1
for n >= 1) and what happens at n = 0 (a zero test if it differs).
Usage: python layer_ops.py LMAX NMAX STEPS BODY   (BODY = N or X)
"""
import sys, collections
sys.setrecursionlimit(100000)
from symb import spine, show, trees
SS = ("S", "S")
B0 = (("S", SS), SS)

def contexts(n):
    """one-hole contexts with n leaves (hole = 'p' counted as a leaf)"""
    if n == 1:
        return ["p"]
    out = []
    for k in range(1, n):
        for L in contexts(k):
            for R in trees(n - k):
                out.append((L, R))
        for L in trees(k):
            for R in contexts(n - k):
                out.append((L, R))
    return out

def body(kind):
    t = B0
    for _ in range(2):
        t = (SS, t) if kind == "N" else ((SS, t), "S")
    return t

def node(head, n, Bt):
    t = head
    for _ in range(n): t = (t, "S")
    return ((t, Bt), "S")

def effect(L, n, Bt, steps):
    K = [node(L, n, Bt), "t1", "t2", "t3"]
    for s in range(steps):
        f = K[0]
        # is the front element p·S^m·B·S ?
        if isinstance(f, tuple) and f[1] == "S" and isinstance(f[0], tuple) and f[0][1] == Bt:
            g = f[0][0]; m = 0
            while isinstance(g, tuple) and g[1] == "S": g = g[0]; m += 1
            if g == "p": return ("next", m, s)
        a = K[0]; ha, aa = spine(a)
        if ha != "S": return ("stuck:" + str(ha), None, s)
        if len(K) < 3: return ("hnf", None, s)
        K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
    return ("budget", None, steps)

if __name__ == "__main__":
    LMAX, NMAX, STEPS, BODY = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    Bt = body(BODY)
    kinds = collections.Counter(); examples = {}
    for nl in range(2, LMAX + 1):
        for L in contexts(nl):
            res = [effect(L, n, Bt, STEPS) for n in range(NMAX + 1)]
            ms = [r[1] if r[0] == "next" else None for r in res]
            if all(m is None for m in ms): continue
            if all(m is not None for m in ms):
                d = [m - n for n, m in enumerate(ms)]
                if len(set(d)) == 1: kind = f"shift {d[0]:+d}"
                else: kind = "other " + str(d)
            else:
                pos = [m for m in ms[1:]]
                if ms[0] is None and all(m is not None for m in pos) and all(pos[j] == j for j in range(len(pos))):
                    kind = "DECREMENT with zero test"
                else:
                    kind = "partial " + str([("-" if m is None else m - n) for n, m in enumerate(ms)])
            kinds[kind] += 1
            examples.setdefault(kind, (show(L).replace("p", "[]"), [(r[0], r[1]) for r in res]))
    print(f"body {BODY}: contexts with a next node:")
    for k, c in kinds.most_common(): print(f"  {c:6d}  {k}   e.g. {examples[k][0]}  {examples[k][1]}")
