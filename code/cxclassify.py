"""Classify infinite head runs whose opcode sequence has superlinear factor complexity (factorcx.py).

For each hnf-free term (NMIN..NMAX leaves) whose p(64) is not bounded/linear, take the opcode with the longest maximal
blocks, list the lengths of its blocks of length >= 5 over STEPS steps, and test (on the last 2/3) whether they are
affine-periodic: L_{j+p} = L_j + c_{j mod p} for some p <= 48 (a single linear counter, possibly interleaved).
Prints counts and the terms that fail (candidates for genuinely richer dynamics).
Usage: python cxclassify.py NMIN NMAX STEPS
"""
import sys, collections
from symb import trees, show
from factorcx import cls, MF, opcodes, pcx
sys.setrecursionlimit(100000)

def blocks_of(seq, op):
    out = []; cur = 0
    for x in seq + [None]:
        if x == op: cur += 1
        else:
            if cur >= 5: out.append(cur)
            cur = 0
    return out

def affine_periodic(L, pmax=48):
    L = L[:-1]                                   # the last block may be cut off by the end of the run
    if len(L) < 12: return None
    L = L[len(L) // 3:]
    for p in range(1, min(pmax, len(L) // 3) + 1):
        incs = {}
        ok = True
        for j in range(len(L) - p):
            d = L[j + p] - L[j]
            r = j % p
            if incs.setdefault(r, d) != d: ok = False; break
        if ok: return p
    return None

if __name__ == "__main__":
    NMIN, NMAX, STEPS = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    stat = collections.Counter(); odd = []
    for n in range(NMIN, NMAX + 1):
        for t in trees(n):
            if MF[cls(t, {})]: continue
            seq = opcodes(t, STEPS)
            if seq is None: continue
            s = seq[STEPS // 3:]
            ps = [pcx(s, m) for m in (8, 16, 32, 64)]
            if ps[-1] <= ps[0] * 1.05 or (ps[3] <= 2.5 * ps[2] and ps[2] <= 2.5 * ps[1]):
                stat["bounded/linear"] += 1; continue
            best = None
            for op in range(4):
                b = blocks_of(seq, op)
                if b and (best is None or max(b) > max(best[1])): best = (op, b)
            if best is None:
                # no long blocks: use the gaps between occurrences of the rarest opcode instead
                gaps_best = None
                for op in range(4):
                    pos = [i for i, x in enumerate(seq) if x == op]
                    g = [b - a for a, b in zip(pos, pos[1:])]
                    if len(g) >= 12 and (gaps_best is None or max(g) > max(gaps_best)): gaps_best = g
                if gaps_best is not None and affine_periodic(gaps_best + [0]):
                    stat["one affine counter (gaps)"] += 1
                else:
                    stat["no long blocks, not affine"] += 1
                    if len(odd) < 25: odd.append((show(t), "gaps", (gaps_best or [])[-20:]))
                continue
            p = affine_periodic(best[1])
            if p: stat["one affine counter"] += 1
            else:
                stat["OTHER"] += 1
                if len(odd) < 25: odd.append((show(t), best[0], best[1][-30:]))
    print(dict(stat))
    for o in odd: print("  ", o)
