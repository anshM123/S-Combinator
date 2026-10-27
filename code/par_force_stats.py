"""How much nested evolution the parallel runs force (main agent, 2026-10-26): lazy_par.force instrumented to count the
sub-machine steps it executes and the largest delay whose forcing executed at least one step. Usage: python par_force_stats.py N"""
import sys, collections
sys.setrecursionlimit(1000000)
import lazy_par as lz
from symb import parse

STEPS = [0]; DEEP = [0]; HIST = collections.Counter()
_force = lz.force
def force(x, k):
    if (x, k) in lz.MEMO: return lz.MEMO[(x, k)]
    st = lz.STATE.get(x); start = 0 if st is None or st[0] > k else st[0]
    before = STEPS[0]
    r = _force(x, k)
    return r
def counted_force(x, k):
    r = lz.MEMO.get((x, k))
    if r is not None: return r
    st = lz.STATE.get(x)
    if st is None or st[0] > k: st = (0, [(e, 0) for e in reversed(lz.plain_spine(x))])
    now, stk = st[0], list(st[1]); did = 0
    while now < k:
        if len(stk) < 3: now = k; break
        (x1, b1), (x2, b2), (x3, b3) = stk.pop(), stk.pop(), stk.pop()
        v1, v2, v3 = lz.delay(x1, now - b1), lz.delay(x2, now - b2), lz.delay(x3, now - b3)
        c = lz.spine(v1); did += 1
        stk.append((lz.app(v2, v3), now + 1)); stk.append((v3, now + 1)); stk.extend((e, now + 1) for e in reversed(c))
        now += 1
    lz.STATE[x] = (now, stk)
    r = [lz.delay(e, k - b) for e, b in reversed(stk)]; lz.MEMO[(x, k)] = r
    STEPS[0] += did
    if did: DEEP[0] = max(DEEP[0], now if len(stk) >= 3 else k); HIST[did] += 1
    return r
lz.force = counted_force

if __name__ == "__main__":
    N = int(sys.argv[1])
    rows = [l.rstrip("\n").split("\t") for l in open("../data/sample_union_150.tsv", encoding="utf-8") if l.strip()]
    tot = collections.Counter()
    for r in rows:
        lz.reset(); STEPS[0] = 0; DEEP[0] = 0; HIST.clear()
        ops = lz.par_ops(r[0], N)
        big = sum(v for d, v in HIST.items() if d > 20)
        print(f"{r[0]:32s} {r[1]:15s} substeps {STEPS[0]:7d} forcings-with-work {sum(HIST.values()):6d} max-work {max(HIST) if HIST else 0:5d} (>20: {big})", flush=True)
