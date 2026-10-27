"""agent_work_J/jump_anatomy.py -- census of the SOURCES of jumps in leftmost walks.
A jump node is S p tau (exactly two arguments); its leftmost child is p.  For the jump node u(j+1) the source is
classified by the predecessor u(j):
  init      : the walk starts at a jump node
  pop       : u(j) = S u(j+1)                       (pop into a jump node)
  jump      : u(j) = S u(j+1) x                     (jump into a jump node)
  tower     : u(j) = q.sigma computed, sigma a tower S(S(..(SS)))
  K0..K3    : u(j) = q.sigma computed over a non-tower sigma, H(q) = S (tw K) c0  (DP.jump_child cases)
              K0 = delayed discard (sigma = S p tau), K1 = discard (c0 = S p), K2 = S-letter (sigma = S.p),
              K3 = c0 = S (target = sigma)
  other     : anything else (should not happen: Lemma Fib)
'sep' jumps = jumps preceded, since the previous jump, by at least one computed step.
usage: python jump_anatomy.py all N NODES | python jump_anatomy.py rand SEED NODES COUNT"""
import sys, time, random
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from late_events import hnf, tree
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, mark, truncate, trees
from classes import cls, LFl, clear_cache
from collections import Counter

def is_tower(x):
    while x != 0:
        if L[x] != 0: return False
        x = R[x]
    return True

def twh(x):
    """height of a tower, or None"""
    k = 0
    while x != 0:
        if L[x] != 0: return None
        x = R[x]; k += 1
    return k

def classify(prev, cur):
    """source of the jump node cur, given predecessor prev"""
    q, v = L[prev], R[prev]
    if q == 0: return "pop"
    a = spine(q)[0]
    if len(a) == 1: return "jump"
    if is_tower(v): return "tower"
    H = hnf(q, 100000) if len(a) >= 2 else None
    if H is None: return "other?"
    K = twh(H[0])
    if K is None: return "other"
    return "K%d" % K

def walk(t, nodes):
    u = t; prev = None; srcs = []; comp_since = 0; seps = 0; last_sep = -1
    for j in range(nodes):
        if u == 0: return "leaf", j, srcs, seps, last_sep
        q, v = L[u], R[u]
        if q != 0 and len(spine(q)[0]) == 1:
            s = "init" if prev is None else classify(prev, u)
            if comp_since > 0: seps += 1; last_sep = j
            srcs.append((j, s, comp_since > 0)); comp_since = 0
        prev = u
        if q == 0: u = v; continue
        a = spine(q)[0]
        if len(a) == 1: u = a[0]; continue
        H = hnf(u, max(20000, 20 * size(u)))
        if H is None: return "bot", j, srcs, seps, last_sep
        u = H[0]; comp_since += 1
        if size(u) > 100000: return "big", j, srcs, seps, last_sep
    return "cap", nodes, srcs, seps, last_sep

if __name__ == "__main__":
    mode = sys.argv[1]
    t0 = time.time(); res = Counter(); src = Counter(); sepsrc = Counter(); best = []; seph = Counter()
    if mode == "all":
        n, nodes = int(sys.argv[2]), int(sys.argv[3]); terms = trees(n); N = len(terms)
    else:
        random.seed(int(sys.argv[2])); nodes = int(sys.argv[3]); terms = None; N = int(sys.argv[4])
    for i in range(N):
        m = mark()
        t = terms[i] if terms is not None else tree(random.randint(2, 7))
        st, ln, srcs, seps, last_sep = walk(t, nodes)
        fl = LFl[cls(t)[0]]
        res[(fl, st)] += 1
        for (_, s, sp) in srcs:
            src[s] += 1
            if sp: sepsrc[s] += 1
        seph[(fl, seps)] += 1
        if seps >= 2:
            best.append((seps, last_sep, st, ln, fl, show(t)[:100], [(j, s) for (j, s, sp) in srcs if sp][:10]))
            best.sort(key=lambda x: (-x[0], -x[1])); best = best[:15]
        if terms is None:
            truncate(m); clear_cache(m)
    print(mode, sys.argv[2:], "time", round(time.time() - t0, 1))
    print("(flag, end) counts:", dict(res))
    print("jump sources (all jumps):", dict(src))
    print("jump sources (computed-separated jumps):", dict(sepsrc))
    print("(flag, #separated jumps) histogram:", dict(sorted(seph.items())))
    print("walks with most separated jumps (seps, last sep index, end, length, flag, term, sep jumps):")
    for b in best: print("  ", b)
