"""same-family HEAD-STYLE contexts (a closed argument follows the hole's spine position somewhere), richer tape
shapes with fuel constants below B; looking for A--/B++ bodies (then a reload could copy B into A)."""
import sys, collections
sys.path.insert(0, r"C:\Users\anshm\Downloads\money problems\code")
from agent_u_ctxnest import run, isC, spine
from agent_u_ctxscan import contexts, BASE
from symb import show
def headstyle(ctx):
    # walk the path to the hole; head-style if at some spine level the hole's argument is followed by an argument
    t = ctx
    while t != "#":
        h, args = spine(t)
        for i, a in enumerate(args):
            if "#" in str(a):
                if i + 1 < len(args): return True
                t = a; break
        else:
            t = h if h != t else "#"
            if t == ctx: return False
    return False
ctxs = [c for c in contexts(6) if headstyle(c)]
F = ["S", ("S", "S")]
shapes = [["J", "B", ("C", c)] for c in F] + [["B", ("C", c), ("C", d)] for c in F for d in F] + \
         [["J", "B", ("C", c), ("C", d)] for c in F for d in F] + [[("C", c), "B", ("C", d)] for c in F for d in F]
cnt = collections.Counter(); hits = []
for c in ctxs:
    fams = [(c, BASE), (c, BASE)]
    for shp in shapes:
        start = [("C", 0, "i", 0)]; js = iter(["j1", "j2"])
        for s in shp: start.append(("C", 1, "k", 0) if s == "B" else (next(js) if s == "J" else s[1]))
        start += ["w1", "w2"]
        def stop(K, br, n, shp=shp):
            if not (isC(K[0]) and K[0][1] == 0): return None
            bk = None
            for s, x in zip(shp, K[1:]):
                if s == "B":
                    if isC(x): bk = x[2:]
                    else: return "front"
                elif s != "J" and x != s[1]: return "front"
            return (K[0][2:], bk)
        out = run(start, fams, stop, maxsteps=60, cap=4)
        body = [o for o in out if o[0].get("i") != ("eq", 0)]
        for o in body:
            l = o[1]; cnt[(l[0][1], l[1][1] if l[1] and l[1][0] == "k" else None) if isinstance(l, tuple) else l] += 1
        good = [o for o in body if isinstance(o[1], tuple) and o[1][0][0] == "i" and o[1][0][1] < 0 and o[1][1] and o[1][1][0] == "k" and o[1][1][1] >= 1]
        if body and len(good) == len(body): hits.append((c, shp, body))
print("contexts", len(ctxs), "shapes", len(shapes)); print(cnt.most_common(12)); print("hits", len(hits))
for h in hits[:10]: print(h)
