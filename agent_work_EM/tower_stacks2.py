"""agent_work_EM/tower_stacks2.py -- variant of tower_stacks.py with tops S (tw K) c, K = 1..3; targeted search for case (b) of EM (depth -> infinity with infinitely many
pops/returns): leftmost walks of nodes q.Z whose stack Z = m_1.(m_2.(...(m_d.base))) is a word over small
multipliers (towers SS, S(SS), S(S(SS)) and a few gadgets), the shape forced in deep jump-free walks by the
gamma lemma (a top A.B over a non-tower bottom with B a non-tower needs A to be a tower).
Reports walks that run NODES nodes (with L36 flag) and walks with pops/jumps/returns after BURN nodes.
usage: python tower_stacks.py MAXLEN NODES BURN"""
import sys, time, itertools
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_EM")
from late_events import walk
sys.path.insert(0, "C:/Users/anshm/Downloads/money problems/agent_work_U")
from dm import app, parse, show, trees, spine, mark, truncate
from classes import cls, LFl, clear_cache
from collections import Counter
ALPH = ["S", "SS", "S(SS)", "S(S(SS))", "S(SS)(SS)", "S(S(SS))(S(SS))"]
BASES = ["S", "SS", "S(SS)(SS)", "S(S(SS))(S(SS))"]
TOPS = ["S(" + k + ")(" + c + ")" for k in ["SS", "S(SS)", "S(S(SS))"] for c in ["S", "SS", "S(SS)", "S(S(SS))", "S(SS)(SS)", "S(S(SS))(S(SS))", "SSS"]] + ["SS(SSS)", "S(SS)(SSS)"]
maxlen, nodes, burn = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
t0 = time.time(); stats = Counter(); late_ex = []; long_ex = Counter(); longs = []
A = [parse(a) for a in ALPH]; Bs = [parse(b) for b in BASES]; Ts = [parse(t) for t in TOPS]
for d in range(0, maxlen + 1):
    for word in itertools.product(range(len(A)), repeat=d):
        for b in Bs:
            Z = b
            for k in reversed(word): Z = app(A[k], Z)
            for q in Ts:
                m = mark()
                u = app(q, Z)
                st, ln, late, first, ev = walk(u, nodes, burn, maxsize=50000)
                fl = LFl[cls(u)[0]]
                stats[(fl, st)] += 1
                if sum(late.values()):
                    stats[(fl, "late")] += 1
                    if len(late_ex) < 15: late_ex.append((fl, st, ln, show(u)[:100], dict(late), ev[:6]))
                if st == "cap":
                    long_ex[fl] += 1
                    if fl == 0 and len(longs) < 10: longs.append(show(u)[:120])
                truncate(m); clear_cache(m)
print("maxlen", maxlen, "nodes", nodes, "burn", burn, "time", round(time.time() - t0, 1), "tops", len(Ts))
print("(flag, status) counts:", dict(stats))
print("walks reaching the node cap, by flag:", dict(long_ex))
print("flag-0 walks reaching the cap (should be none):", longs)
print("walks with late pops/jumps/returns (flag, status, length, term, kinds, first events):")
for e in late_ex: print("   ", e)
