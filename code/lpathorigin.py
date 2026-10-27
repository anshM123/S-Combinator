"""Along the leftmost Böhm-tree path, track which ORIGINAL leaf of t is the head S of each node.
Residuals are shared objects (the head machine only shares c and creates b.c), so object identity = origin.
Reports: for finite paths, whether head-leaf origins are pairwise distinct; for unfinished paths, when the first
repetition occurs."""
import sys
sys.setrecursionlimit(100000)
from symb import trees, show

class T:
    __slots__ = ("l", "r", "id")
    cnt = 0
    def __init__(self, l=None, r=None):
        self.l, self.r = l, r
        T.cnt += 1; self.id = T.cnt
def build(t):
    if t == "S": return T()
    return T(build(t[0]), build(t[1]))
def spine_args(e):
    args = []
    while e.l is not None: args.append(e.r); e = e.l
    args.reverse(); return e, args          # head leaf object, args
def size(e):
    st = [e]; k = 0
    while st:
        u = st.pop()
        if u.l is None: k += 1
        else: st.append(u.l); st.append(u.r)
    return k
def hnf(e, budget):
    head, args = spine_args(e)
    lst = list(args); steps = 0
    while len(lst) >= 3:
        if steps >= budget: return None
        a, b, c = lst[0], lst[1], lst[2]
        _, ch = spine_args(a)
        lst = ch + [c, T(b, c)] + lst[3:]
        steps += 1
    return lst
def run(n, maxd=200):
    stats = {"finite": 0, "finite_distinct": 0, "unfinished": 0, "first_rep": []}
    viol = []
    for t in trees(n):
        e = build(t); heads = []; d = 0; ended = False
        while d < maxd:
            h, _ = spine_args(e)
            heads.append(h.id)
            lst = hnf(e, 4 * size(e) + 200)
            if lst is None or len(lst) == 0: ended = True; break
            e = lst[0]; d += 1
            if size(e) > 50000: break
        if ended:
            stats["finite"] += 1
            if len(set(heads)) == len(heads): stats["finite_distinct"] += 1
            else: viol.append((show(t), d))
        else:
            stats["unfinished"] += 1
            seen = {}
            for i, h in enumerate(heads):
                if h in seen: stats["first_rep"].append(i); break
                seen[h] = i
    return stats, viol
for n in range(3, int(sys.argv[1]) + 1):
    st, viol = run(n)
    fr = st["first_rep"]
    print(f"n={n:2d} finite paths {st['finite']:6d}, with distinct head origins {st['finite_distinct']:6d}; "
          f"unfinished {st['unfinished']}, first repeat at depth {sorted(set(fr))[:5]}", flush=True)
    for v in viol[:3]: print("     repeat on a finite path:", v)
