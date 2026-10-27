"""(A) with general A contexts: front = A_i . fuel, B = wrapper ctx V.# (twist-built), tape shapes."""
import sys, collections
sys.path.insert(0, r"C:\Users\anshm\Downloads\money problems\code")
from agent_u_ctxnest import run, isC, spine
from agent_u_ctxscan import contexts, BASE
from symb import trees, show
small = [t for n in range(1, 4) for t in trees(n)]
fuels = [[]] + [[c] for c in small] + [[c, d] for c in ("S", ("S", "S")) for d in ("S", ("S", "S"))]
shapes = [["J", "B"], ["B", "J"]] + [[("C", c), "B"] for c in small]
cnt = collections.Counter(); hits = []
for cA in contexts(4):
    for V in small:
        fams = [(cA, BASE), ((V, "#"), BASE)]
        for fuel in fuels:
            for shp in shapes:
                front = ("C", 0, "i", 0)
                for f in fuel: front = (front, f)
                start = [front]; js = iter(["j1", "j2"])
                for s in shp: start.append(("C", 1, "k", 0) if s == "B" else (next(js) if s == "J" else s[1]))
                start += ["w1", "w2"]
                def stop(K, br, n, shp=shp, fuel=fuel):
                    h, a = spine(K[0])
                    if not (isC(h) and h[1] == 0 and a == list(fuel)): return None
                    bk = None
                    for s, x in zip(shp, K[1:]):
                        if s == "B":
                            if isC(x) and x[1] == 1: bk = x[2:]
                            else: return "front"
                        elif s != "J" and x != s[1]: return "front"
                    return (h[2:], bk)
                out = run(start, fams, stop, maxsteps=60, cap=4)
                body = [o for o in out if o[0].get("i") != ("eq", 0)]
                for o in body:
                    l = o[1]
                    cnt[(l[0][1], l[1][1] if l[1] and l[1][0] == "k" else None) if isinstance(l, tuple) else l] += 1
                good = [o for o in body if isinstance(o[1], tuple) and o[1][0][0] == "i" and o[1][0][1] < 0 and o[1][1] and o[1][1][0] == "k" and o[1][1][1] >= 1]
                if body and len(good) == len(body): hits.append((cA, show(V), fuel, shp, body))
print(cnt.most_common(15)); print("hits", len(hits))
for h in hits[:15]: print(h)
