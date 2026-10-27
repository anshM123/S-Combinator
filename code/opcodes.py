"""Opcode sequences of infinite head runs (terms without hnf = what leftmost-outermost evaluation does forever).

For each M35-bottom term (no hnf, Theorem A) with <= NMAX leaves, run STEPS head steps and record, for every step, the
spine length of the opened front element (0, 1, 2, 3 = '3 or more'). Classify the sequence after a transient:
eventually periodic (period <= 64), or 'counter-like' (run-length encoding whose block lengths grow by a fixed
arithmetic pattern), or other. Prints statistics and the 'other' examples (run-length encoded).
Usage: python opcodes.py NMAX STEPS
"""
import sys, collections
from verify_model import load
from symb import trees, show, spine

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

def eventually_periodic(seq, maxp=64, tail=600):
    s = seq[-tail:]
    for p in range(1, maxp + 1):
        if all(s[i] == s[i + p] for i in range(len(s) - p)): return p
    return None

def rle(seq):
    out = []
    for x in seq:
        if out and out[-1][0] == x: out[-1][1] += 1
        else: out.append([x, 1])
    return out

if __name__ == "__main__":
    NMAX, STEPS = int(sys.argv[1]), int(sys.argv[2])
    stat = collections.Counter(); others = []
    for n in range(4, NMAX + 1):
        for t in trees(n):
            if MF[cls(t, {})]: continue
            seq = opcodes(t, STEPS)
            if seq is None: stat["hnf?"] += 1; continue
            p = eventually_periodic(seq)
            if p is not None: stat[f"periodic"] += 1; continue
            # counter-like: block structure of the sequence of 'separator' positions
            r = rle(seq[STEPS // 3:])
            lens = [k for (x, k) in r if x == r[0][0]]
            stat["aperiodic"] += 1
            if len(others) < 12: others.append((show(t), [tuple(b) for b in r[:24]]))
    print(dict(stat))
    for o in others: print("  ", o)
