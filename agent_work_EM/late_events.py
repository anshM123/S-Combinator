"""agent_work_EM/late_events.py -- census of LATE non-monotone events (pops, jumps, returns) in leftmost walks.
For each term: run the leftmost walk up to NODES nodes; each step is classified as pop (node S v), jump (node S p v),
ret (computed, child = last argument), tail (computed, depth kept), push (computed, depth grows).  Reports, per L36
flag, the walks with the most pops/jumps/returns after a burn-in, and how long walks with late events run.
usage: python late_events.py MODE ARG NODES BURN
  MODE = all  : all closed terms with ARG leaves (exhaustive)
  MODE = rand : ARG random gadget compositions (seeded)"""
import sys, time, random
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, trees, mark, truncate, parse
from classes import cls, LFl, clear_cache
from collections import Counter
def hnf(u, bud):
    a, h = spine(u)
    st = list(reversed(a)); k = 0
    while len(st) > 2:
        x = st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
        if k > bud: return None
    return list(reversed(st))
def depth(u):
    d = 0
    while u != 0: u = R[u]; d += 1
    return d
def walk(t, nodes, burn, maxsize=200000):
    """returns (status, length, late Counter, first-late-index, events list (late only, truncated))"""
    u = t; late = Counter(); first = None; ev = []
    d = depth(u)
    for j in range(nodes):
        if u == 0: return "leaf", j, late, first, ev
        q, v = L[u], R[u]
        if q == 0: kind = "pop"; nu = v
        else:
            a = spine(q)[0]
            if len(a) == 1: kind = "jump"; nu = a[0]
            else:
                H = hnf(u, max(20000, 20 * size(u)))
                if H is None: return "bot", j, late, first, ev
                nu = H[0]
                if nu == v: kind = "ret"
                else:
                    nd = depth(nu)
                    kind = "tail" if nd == d else ("push" if nd > d else "other")
        if j >= burn and kind in ("pop", "jump", "ret", "other"):
            late[kind] += 1
            if first is None: first = j
            if len(ev) < 12: ev.append((j, kind, d))
        u = nu; d = depth(u)
        if size(u) > maxsize: return "big", j, late, first, ev
    return "cap", nodes, late, first, ev
G = ["S", "SS", "S(SS)", "S(SS)(SS)", "S(S(SS))(S(SS))", "SS(S(SS)(SS))", "S(SS)(S(S(SS))(S(SS)))", "SSS", "S(SSS)",
     "S(S(SS))", "SS(SS)", "S(S(SS))S", "SSSS", "S(SS)S"]
def rand_term(n):
    if n == 1: return 0
    k = random.randint(1, n - 1)
    return app(rand_term(k), rand_term(n - k))
def tree(n):
    if n == 1:
        return parse(random.choice(G)) if random.random() < 0.7 else rand_term(random.randint(2, 7))
    k = random.randint(1, n - 1)
    return app(tree(k), tree(n - k))
if __name__ == "__main__":
    mode, arg, nodes, burn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    t0 = time.time(); stats = Counter(); best = {0: [], 1: []}
    if mode == "all":
        terms = trees(arg)
    else:
        random.seed(arg); terms = None
    N = len(terms) if terms is not None else int(sys.argv[5])
    for i in range(N):
        m = mark()
        t = terms[i] if terms is not None else tree(random.randint(2, 7))
        fl = LFl[cls(t)[0]]
        st, ln, late, first, ev = walk(t, nodes, burn)
        stats[(fl, st)] += 1
        tot = sum(late.values())
        if tot:
            stats[(fl, "has_late")] += 1
            best[fl].append((tot, ln, st, show(t)[:90], dict(late), ev[:8]))
            best[fl].sort(key=lambda x: (-x[0], -x[1])); best[fl] = best[fl][:12]
        if terms is None:
            truncate(m); clear_cache(m)
    print(mode, arg, "nodes", nodes, "burn", burn, "time", round(time.time() - t0, 1))
    print("(flag, status) counts:", dict(stats))
    for fl in (0, 1):
        print("flag", fl, "walks with most late pops/jumps/returns (count, length, status, term, kinds, first events (j,kind,depth)):")
        for b in best[fl]: print("   ", b)
