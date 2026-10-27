"""agent_work_EM/tp_check.py -- evidence for the two conjectures left by DP.finite_half_of_J_TP:
 (J)  an infinite leftmost walk makes only finitely many jumps;
 (TP) a deep (depth -> infinity) jump-free infinite walk eventually has only non-tower stacks and every computed step
      pushing K >= 2 multipliers is a K = 2 push of a tower letter tw (k+1) (H(q) = S (tw 2) (tw (k+1))).
Families: self-applications X X, X X S, S X X, X (S X) for all closed X with n leaves (MODE self), or tower-stack
starts q.Z as in tower_stacks2.py (MODE tower).  Walks of NODES nodes that do not end are split into deep and
bounded-depth ones; for deep walks the second half is checked against TP and J.
usage: python tp_check.py self N NODES  |  python tp_check.py tower MAXLEN NODES"""
import sys, time, itertools
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from late_events import hnf, depth
from deep_structure import steps, is_tower
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import L, R, app, spine, size, show, mark, truncate, parse, trees
from classes import cls, LFl, clear_cache
from collections import Counter
mode, n, nodes = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
t0 = time.time(); res = Counter(); tally = Counter(); bad = []
def terms():
    if mode == "self":
        for X in trees(n):
            yield app(X, X); yield app(app(X, X), 0); yield app(app(0, X), X); yield app(X, app(0, X))
    else:
        ALPH = [parse(a) for a in ["S", "SS", "S(SS)", "S(S(SS))", "S(SS)(SS)", "S(S(SS))(S(SS))"]]
        BASES = [parse(b) for b in ["S", "SS", "S(SS)(SS)", "S(S(SS))(S(SS))"]]
        TOPS = [parse("S(" + k + ")(" + c + ")") for k in ["SS", "S(SS)", "S(S(SS))"]
                for c in ["S", "SS", "S(SS)", "S(S(SS))", "S(SS)(SS)", "S(S(SS))(S(SS))", "SSS"]]
        for d in range(n + 1):
            for word in itertools.product(range(len(ALPH)), repeat=d):
                for b in BASES:
                    Z = b
                    for k in reversed(word): Z = app(ALPH[k], Z)
                    for q in TOPS: yield app(q, Z)
for t in terms():
    m = mark()
    if LFl[cls(t)[0]] == 1:
        out, ds = steps(t, nodes)
        if out is None: res["ends/bot/big"] += 1
        else:
            half = nodes // 2
            deep = min(ds[half:]) > min(ds[half // 2: half]) + 2
            res["deep" if deep else "bounded"] += 1
            for (kind, K, c) in out[half:]:
                if kind == "jump": tally["jump (J violation)"] += 1
                if deep:
                    key = (kind, K, c if K in (2, 3) else "")
                    tally[key] += 1
                    ok = (kind == "step" and (K == 1 or (K == 2 and c in ("SS", "S(SS)", "S(S(SS))"))))
                    if not ok and len(bad) < 10: bad.append((show(t)[:80], kind, K, c))
    else:
        res["flag0 (not walked)"] += 1
    truncate(m); clear_cache(m)
print(mode, n, "nodes", nodes, "time", round(time.time() - t0, 1))
print("terms:", dict(res))
print("second-half step tally (deep walks; jumps counted in all long walks):", dict(tally))
print("TP violations in deep walks (term, kind, K, c0):", bad)
