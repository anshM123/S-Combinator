"""agent_work_EM/deep_structure.py -- test the predicted structure of deep infinite walks (LOG 11:02 / 11:2x sketch):
after burn-in, every step of a deep (depth -> infinity) jump-free walk is a Fibonacci step K in {1, 2} (no pops,
returns, jumps, K = 3), and every K = 2 step pushes c0 = S(SS) (the letter tw2), i.e. the walk is a generalized
Omega cycle.  Collects long walks (flag 1, NODES nodes) from random gadget compositions, splits them into
bounded-depth (Scenario A) and deep ones, and tallies (K, c0) over the second half of each deep walk.
usage: python deep_structure.py SEED N NODES"""
import sys, time, random
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from late_events import hnf, depth, tree, walk
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, mark, truncate, parse
from classes import cls, LFl, clear_cache
from collections import Counter
def is_tower(t):
    while t != 0:
        if L[t] != 0: return False
        t = R[t]
    return True
def tw_index(t):
    k = 0
    while t != 0:
        if L[t] != 0: return None
        t = R[t]; k += 1
    return k
def steps(t, nodes):
    """per node: (kind, K, c0 as string) for computed nodes over non-tower bottoms"""
    u = t; out = []; ds = []
    for j in range(nodes):
        if u == 0: return None, None
        q, v = L[u], R[u]
        ds.append(depth(u))
        if q == 0: out.append(("pop", None, None)); u = v; continue
        a = spine(q)[0]
        if len(a) == 1: out.append(("jump", None, None)); u = a[0]; continue
        hq = hnf(q, 20000)
        H = hnf(u, max(20000, 20 * size(u)))
        if H is None or hq is None or len(hq) != 2: return None, None
        x0, c0 = hq
        K = tw_index(x0)
        nu = H[0]
        kind = "ret" if nu == v else "step"
        if is_tower(v): kind += "/towerbottom"
        out.append((kind, K, show(c0)[:20]))
        u = nu
        if size(u) > 300000: return None, None
    return out, ds
if __name__ == "__main__":
    seed, N, nodes = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    random.seed(seed); t0 = time.time()
    deep = 0; shallow = 0; tally = Counter(); bad = []
    for i in range(N):
        m = mark()
        t = tree(random.randint(2, 7))
        if LFl[cls(t)[0]] == 1:
            out, ds = steps(t, nodes)
            if out is not None:
                half = nodes // 2
                if min(ds[half:]) > min(ds[half // 2: half]) + 2:
                    deep += 1
                    for (kind, K, c) in out[half:]:
                        key = (kind, K, c if K in (2, 3) else "")
                        tally[key] += 1
                        if (kind != "step" or K not in (1, 2) or (K == 2 and c != "S(SS)")) and len(bad) < 10:
                            bad.append((show(t)[:80], kind, K, c))
                else:
                    shallow += 1
        truncate(m); clear_cache(m)
    print("seed", seed, "N", N, "nodes", nodes, "time", round(time.time() - t0, 1))
    print("long flag-1 walks: deep", deep, "bounded-depth", shallow)
    print("(kind, K, c0 at K=2/3) over the second halves of the deep walks:", dict(tally))
    print("deviations from the generalized-Omega prediction:", bad)
