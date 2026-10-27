"""Along the rightmost Böhm-tree path: is the original LAST spine argument of the root ever opened (read)?
Object identity tracks residuals.  If never, the rightmost path is a pure pushdown process on that element."""
import sys
sys.setrecursionlimit(100000)
from symb import trees, show
class T:
    __slots__ = ("l", "r")
    def __init__(self, l=None, r=None): self.l, self.r = l, r
def build(t):
    if t == "S": return T()
    return T(build(t[0]), build(t[1]))
def spine_args(e):
    args = []
    while e.l is not None: args.append(e.r); e = e.l
    args.reverse(); return args
def sz(e):
    st = [e]; k = 0
    while st:
        u = st.pop()
        if u.l is None: k += 1
        else: st.append(u.l); st.append(u.r)
    return k
def nodes_of(e, out):
    st = [e]
    while st:
        u = st.pop(); out.add(id(u))
        if u.l is not None: st.append(u.l); st.append(u.r)
    return out
def run(n, depth=60):
    read_cnt = total = infinite = 0
    for t in trees(n):
        root = build(t); args = spine_args(root)
        if len(args) < 3: continue
        last = nodes_of(args[-1], set()); e = root; was_read = False; d = 0; ended = False
        while d < depth:
            lst = spine_args(e); steps = 0
            while len(lst) >= 3:
                if steps > 4 * sz(e) + 200: lst = None; break
                a, b, c = lst[0], lst[1], lst[2]
                x = a
                while True:                      # mark the left spine of the opened element
                    if id(x) in last: was_read = True
                    if x.l is None: break
                    x = x.l
                lst = spine_args(a) + [c, T(b, c)] + lst[3:]; steps += 1
            if lst is None or len(lst) == 0: ended = True; break
            e = lst[-1]; d += 1
            if sz(e) > 30000: break
        total += 1; read_cnt += was_read; infinite += (not ended)
    return total, read_cnt, infinite
for n in range(4, int(sys.argv[1]) + 1):
    tot, rd, inf = run(n)
    print(f"n={n:2d} terms with >=3 args {tot:6d}: last argument read along the rightmost path in {rd:6d}; unfinished paths {inf}", flush=True)
