"""agent_work_J/jump_climb.py -- hill-climbing search for leftmost walks with MANY separated jumps (jumps preceded,
since the previous jump, by at least one computed step).  Score = (#separated jumps, walk length).  Mutations replace a
random subterm by a random gadget composition.  Terms are capped at MAXLEAVES leaves.
usage: python jump_climb.py SEED MINUTES MAXLEAVES NODES"""
import sys, time, random
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from late_events import hnf, tree
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, mark, truncate, parse
from classes import cls, LFl, clear_cache
def walk(t, nodes):
    u = t; comp = 0; seps = 0; js = []
    for j in range(nodes):
        if u == 0: return seps, j, "leaf", js
        q, v = L[u], R[u]
        if q == 0: u = v; continue
        a = spine(q)[0]
        if len(a) == 1:
            if comp > 0: seps += 1; js.append(j)
            comp = 0; u = a[0]; continue
        H = hnf(u, max(5000, 10 * size(u)))
        if H is None: return seps, j, "bot", js
        u = H[0]; comp += 1
        if size(u) > 20000: return seps, j, "big", js
    return seps, nodes, "cap", js
def subterms(t):
    out = []; st = [t]
    while st:
        x = st.pop(); out.append(x)
        if x > 0: st.append(L[x]); st.append(R[x])
    return out
def replace(t, target_idx, new):
    # replace the target_idx-th node in preorder (same order as subterms) by new
    cnt = [0]
    def rec(x):
        i = cnt[0]; cnt[0] += 1
        if i == target_idx: return new
        if x <= 0: return x
        l = rec(L[x]); r = rec(R[x])
        return app(l, r)
    return rec(t)
def preorder_count(t):
    return len(subterms(t))
if __name__ == "__main__":
    seed, minutes, maxl, nodes = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    random.seed(seed); t0 = time.time(); best_overall = []
    restarts = 0
    while time.time() - t0 < minutes * 60:
        restarts += 1
        m0 = mark()
        cur = tree(random.randint(3, 8))
        while size(cur) > maxl: cur = tree(random.randint(3, 6))
        m1 = mark(); cs = walk(cur, nodes); truncate(m1); clear_cache(m1)
        for it in range(300):
            n = preorder_count(cur)
            idx = random.randrange(n)
            new = tree(random.randint(1, 4)) if random.random() < 0.8 else 0
            cand = replace(cur, idx, new)
            if size(cand) > maxl: continue
            m2 = mark()
            s = walk(cand, nodes)
            truncate(m2); clear_cache(m2)
            if (s[0], s[1]) >= (cs[0], cs[1]):
                cur, cs = cand, s
        fl = LFl[cls(cur)[0]]
        best_overall.append((cs[0], cs[1], cs[2], fl, show(cur)[:160], cs[3][:12]))
        best_overall.sort(key=lambda x: (-x[0], -x[1])); best_overall = best_overall[:12]
        truncate(m0); clear_cache(m0)
    print("seed", seed, "minutes", minutes, "maxleaves", maxl, "nodes", nodes, "restarts", restarts)
    print("best (separated jumps, walk length, end, flag, term, separated-jump indices):")
    for b in best_overall: print("  ", b)
