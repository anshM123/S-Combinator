import sys, collections, itertools
sys.path.insert(0, r"C:\Users\anshm\Downloads\money problems\code")
from agent_u_ctxnest import run, isC, spine
from symb import trees, show
def contexts(maxn):
    out = []
    def holes(t):
        if t == "S": yield "#"; return
        for l in holes(t[0]): yield (l, t[1])
        for r in holes(t[1]): yield (t[0], r)
    for n in range(2, maxn + 1):
        for t in trees(n):
            out.extend(holes(t))
    return out
def sh(c): return show(c).replace("#", "#") if False else str(c)
small = [t for n in range(1, 4) for t in trees(n)]
BASE = (("S", ("S", "S")), ("S", "S"))
shapes = [["J", "B"], ["B", "J"]] + [[("C", c), "B"] for c in small] + [["J", ("C", c), "B"] for c in small] + [["B", ("C", c)] for c in small]
def scan(ctxA_list, ctxB_list, same):
    res = []; cnt = collections.Counter()
    for cA in ctxA_list:
        for cB in ([cA] if same else ctxB_list):
            fams = [(cA, BASE), (cB, BASE)]
            for shp in shapes:
                start = [("C", 0, "i", 0)]; js = iter(["j1", "j2"])
                for s in shp:
                    start.append(("C", 1, "k", 0) if s == "B" else (next(js) if s == "J" else s[1]))
                start += ["w1", "w2"]
                def stop(K, br, n, shp=shp):
                    if not (isC(K[0]) and K[0][1] == 0): return None
                    if len(K) <= len(shp): return None
                    bk = None
                    for s, x in zip(shp, K[1:]):
                        if s == "B":
                            if isC(x) and x[1] == 1: bk = x[2:]
                            else: return ("front", K[0][2:])
                        elif s != "J" and x != s[1]: return ("front", K[0][2:])
                    return (K[0][2:], bk)
                out = run(start, fams, stop, maxsteps=60, cap=4)
                body = [o for o in out if o[0].get("i") != ("eq", 0)]
                for o in body:
                    lab = o[1]
                    if isinstance(lab, tuple) and lab[0] != "front": cnt[(lab[0][1], lab[1][1] if lab[1][0] == "k" else ("x", lab[1]))] += 1
                    else: cnt[lab if isinstance(lab, str) else "front"] += 1
                good = [o for o in body if isinstance(o[1], tuple) and o[1][0] != "front" and o[1][0][0] == "i" and o[1][0][1] < 0 and o[1][1][0] == "k" and o[1][1][1] >= 1]
                if body and len(good) == len(body): res.append((cA, cB, shp, body))
    return res, cnt
if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "same":
        res, cnt = scan(contexts(5), None, True)
    else:
        c4 = contexts(4); res, cnt = scan(c4, c4, False)
    print(cnt.most_common(20)); print("hits", len(res))
    for r in res[:15]: print(r)
