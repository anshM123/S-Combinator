"""Scenario-A hunt guided by the rightmost path: in Scenario A the multiplier above the frozen fuel traces an infinite
rightmost path, so candidates are q with an R19 flag-1 class (proved infinite rightmost path, main agent's Prop. Q'').
For all such q <= n leaves and fuels Z in a small list, walk q.Z along the leftmost path (<= NODES nodes).  Report
(i) walks that run NODES nodes and their L36 flag, (ii) whether the walk keeps depth >= depth(Z)+1 (Z frozen)."""
import sys, time
from dm import *
from classes import cls, LFl, MFl, load, BASE, clear_cache
from collections import Counter
Rr, RF, RT = load(BASE + "model19_rightpath.txt")
RTl = RT.tolist(); RFl = RF.tolist(); sR = Rr.index("S")
_RC = {}
def rcls(i):
    if i == 0: return sR
    r = _RC.get(i)
    if r is not None: return r
    st = [i]
    while st:
        j = st[-1]
        if j == 0 or j in _RC: st.pop(); continue
        pend = [k for k in (L[j], R[j]) if k != 0 and k not in _RC]
        if pend: st.extend(pend); continue
        a = sR if L[j] == 0 else _RC[L[j]]; b = sR if R[j] == 0 else _RC[R[j]]
        _RC[j] = RTl[a][b]; st.pop()
    return _RC[i]
NODES = 300
def rdepth(u):
    d = 0
    while u != 0: u = R[u]; d += 1
    return d
def walk(u, dz):
    frozen = True
    for j in range(NODES):
        if u == 0: return "S", j, frozen
        if rdepth(u) <= dz: frozen = False
        q1, v = L[u], R[u]
        if q1 == 0: u = v; continue
        a = spine(q1)[0]
        if len(a) == 1: u = a[0]; frozen = False; continue
        st = list(reversed(spine(u)[0])); k = 0; bud = max(3000, 20 * size(u))
        while len(st) > 2:
            x = st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c); st.extend(reversed(spine(x)[0])); k += 1
            if k > bud: return "bot?", j, frozen
        u = st[-1]
        if size(u) > 100000: return "huge", j, frozen
    return "long", NODES, frozen
def trees(n):
    if n == 1: yield 0; return
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k): yield app(l, r)
Zs = [parse(z) for z in ["S", "SS", "SSS", "S(SS)"]]
stat = Counter(); t0 = time.time(); nq = 0
for n in range(1, int(sys.argv[1]) + 1):
    for q in trees(n):
        if RFl[rcls(q)] != 1: continue
        nq += 1
        for Z in Zs:
            t = app(q, Z); c = cls(t)
            if MFl[c[1]] == 0: stat[("noHNF",)] += 1; continue
            w, j, fr = walk(t, rdepth(Z))
            stat[(show(Z), w, LFl[c[0]], fr if w == "long" else None)] += 1
            if w in ("long", "huge") and LFl[c[0]] == 0: print("CANDIDATE", show(t), c, w, fr, flush=True)
    print(n, "R19-flag-1 multipliers so far:", nq, round(time.time() - t0), "s", flush=True)
for k, v in sorted(stat.items(), key=str): print(k, v)
