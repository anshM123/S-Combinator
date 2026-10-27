"""Behavioural complexity of infinite head runs, measured by factor complexity.

For every hnf-free S-term (M35 class bottom, Theorem A) with NMIN..NMAX leaves, run STEPS head steps and record the
opcode sequence (spine length of the opened front element, capped at 3). On the last 2/3 of the sequence compute
p(m) = number of distinct length-m factors for m = 8, 16, 32, 64. Eventually periodic runs have bounded p; one counter
(blocks growing by a fixed pattern) gives p(m) roughly linear in m; anything growing faster is reported.
Usage: python factorcx.py NMIN NMAX STEPS
"""
import sys, collections
from verify_model import load
from symb import trees, show, spine
sys.setrecursionlimit(100000)

Mr, MF, MT = load("../data/model35_hn.txt"); sM = Mr.index("S")

def cls(t, memo):
    if t == "S": return sM
    r = memo.get(id(t))
    if r is None:
        r = int(MT[cls(t[0], memo), cls(t[1], memo)]); memo[id(t)] = r
    return r

def opcodes(t, steps):
    h, K = spine(t); K = list(K); out = []
    for _ in range(steps):
        if len(K) < 3: return None
        a, b, c = K[0], K[1], K[2]
        _, aa = spine(a)
        out.append(min(len(aa), 3))
        K = list(aa) + [c, (b, c)] + K[3:]
    return out

def pcx(seq, m):
    return len({tuple(seq[i:i + m]) for i in range(len(seq) - m + 1)})

if __name__ == "__main__":
    NMIN, NMAX, STEPS = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rows = []
    for n in range(NMIN, NMAX + 1):
        for t in trees(n):
            if MF[cls(t, {})]: continue
            seq = opcodes(t, STEPS)
            if seq is None: continue
            s = seq[STEPS // 3:]
            ps = [pcx(s, m) for m in (8, 16, 32, 64)]
            rows.append((ps, show(t)))
    kinds = collections.Counter()
    for ps, t in rows:
        if ps[-1] <= ps[0] * 1.05: kinds["bounded"] += 1
        elif ps[3] <= 2.5 * ps[2] and ps[2] <= 2.5 * ps[1]: kinds["~linear"] += 1
        else: kinds["superlinear"] += 1
    print(f"hnf-free terms analysed: {len(rows)}; {dict(kinds)}")
    rows.sort(key=lambda r: -r[0][3])
    print("highest p(64):")
    for ps, t in rows[:12]: print("   ", ps, t)
