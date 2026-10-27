"""Sharper behaviour classifier for infinite head runs (main agent).

Classes: 'bounded/linear' (factor complexity), 'single counter' (affine-periodic blocks or gaps), 'binary counter'
(long gaps of some opcode = a constant base value interleaved with lo + step*v2(k + off), <= 5% mismatches after a
transient), 'nested counter' (block/gap values constant over stretches whose values and lengths are each affine),
'OTHER'. Used by lo_census2.py.
"""
import collections
from factorcx import opcodes, pcx
from cxclassify import blocks_of, affine_periodic

def v2(n):
    c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c

def ruler_fit(g):
    """g: list of long gaps. Return True if g = base interleaved with lo + step*v2(k+off) (<= 5% mismatches)."""
    if len(g) < 60: return False
    base = collections.Counter(g).most_common(1)[0][0]
    rest = [x for x in g if x != base]
    if len(rest) < 40: return False
    tail = rest[len(rest) // 5:]
    k0 = len(rest) - len(tail)
    vals = sorted(set(tail))
    for lo in vals[:3]:
        for step in range(1, 13):
            for off in range(0, 16):
                mism = 0
                for j, x in enumerate(tail):
                    if x != lo + step * v2(j + 1 + k0 + off):
                        mism += 1
                        if mism > 0.05 * len(tail): break
                if mism <= 0.05 * len(tail): return True
    return False

def nested_fit(L):
    L = L[:-1]
    if len(L) < 40: return False
    runs = []
    for x in L:
        if runs and x == runs[-1][0]: runs[-1][1] += 1
        else: runs.append([x, 1])
    if len(runs) < 6: return False
    vals = [r[0] for r in runs][1:-1]; lens = [r[1] for r in runs][1:-1]
    return affine_periodic(vals + [0]) is not None and affine_periodic(lens + [0]) is not None

def classify(u, steps):
    seq = opcodes(u, steps)
    if seq is None: return "hnf?"
    s = seq[steps // 3:]
    ps = [pcx(s, m) for m in (8, 16, 32, 64)]
    if ps[-1] <= ps[0] * 1.05 or (ps[3] <= 2.5 * ps[2] and ps[2] <= 2.5 * ps[1]): return "bounded/linear"
    for op in range(4):
        b = blocks_of(seq, op)
        if b and affine_periodic(b): return "single counter"
    gaps = {}
    for op in range(4):
        pos = [i for i, x in enumerate(seq) if x == op]
        g = [b - a for a, b in zip(pos, pos[1:])]
        gaps[op] = g
        if len(g) >= 12 and affine_periodic(g + [0]): return "single counter"
    for op in range(4):
        big = [x for x in gaps[op] if x > 6]
        if ruler_fit(big): return "binary counter"
    for op in range(4):
        b = blocks_of(seq, op)
        if b and nested_fit(b): return "nested counter"
        big = [x for x in gaps[op] if x > 6]
        if nested_fit(big): return "nested counter"
    return "OTHER"
