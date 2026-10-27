"""Disprover: exact counter programs of leftmost walks with THREE nest slots, nodes ((N_i N_k) N_m) R.

Uses the exact symbolic interpreter of nestwalk.py (opening a nest branches on n = 0 / n >= 1; W-applications folded).
For each family (wrapper W, bases B1, B2, B3, tail R) we follow the walk until the node again has the shape
((N(B1') N(B2')) N(B3')) R' with bases from the pool (state changes allowed) and record the guarded transition on
(i, k, m). Classifies transitions: countdown (one counter -1), copy/reset (a counter takes another's value), increment
(+1), TRANSFER (one -1 and another +1 in the same transition) and reports any family with a transfer or with a counter
that is both incremented and decremented in its program.
Usage: python walk3.py BASEMAX TAILMAX STEPS
"""
import sys, itertools, collections
import nestwalk as nw
from symb import trees, show

BASEMAX, TAILMAX, STEPS = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
W = [("S", "S")]
pool = [t for n in range(1, BASEMAX + 1) for t in trees(n)]
Rs = [t for n in range(1, TAILMAX + 1) for t in trees(n)]

def nest(e):
    return (e[2], e[3], e[4]) if isinstance(e, tuple) and len(e) == 5 and e[0] == "N" else None

def match3(node):
    if not (isinstance(node, tuple) and node[0] != "N"): return None
    p, R = node
    if R not in Rs or not (isinstance(p, tuple) and p[0] != "N"): return None
    q, c = p
    if not (isinstance(q, tuple) and q[0] != "N"): return None
    a, b = q
    na, nb, nc = nest(a), nest(b), nest(c)
    if na and nb and nc: return (na, nb, nc, R)
    return None

def family(b1, b2, b3, R):
    start = (((("N", 0, b1, "i", 0), ("N", 0, b2, "k", 0)), ("N", 0, b3, "m", 0)), R)
    out = []; work = [(start, nw.Br({}), 0)]
    while work:
        node, br, n = work.pop()
        if n > 0:
            m = match3(node)
            if m is not None: out.append((dict(br.cons), m)); continue
        if n >= STEPS: continue
        for (K0, b0) in nw.open_el(node, W, pool, br):
            for (Kf, b1_) in nw.hnf(K0, W, pool, b0):
                if Kf: work.append((nw.fold(Kf[0], W), b1_, n + 1))
    return out

def classify(tr):
    kinds = set()
    old = {"i": 0, "k": 1, "m": 2}
    news = [tr[0][1:], tr[1][1:], tr[2][1:]]          # (var, offset) per slot
    deltas = []
    for slot, (v, d) in enumerate(news):
        if v is None: deltas.append(("const", d)); continue
        if old[v] == slot: deltas.append(("self", d))
        else: deltas.append(("copy", v, d))
    if any(x[0] == "copy" for x in deltas): kinds.add("copy")
    dec = [s for s, x in enumerate(deltas) if x[0] == "self" and x[1] < 0]
    inc = [s for s, x in enumerate(deltas) if x[0] in ("self", "copy") and x[-1] > 0]
    if dec: kinds.add("dec")
    if inc: kinds.add("inc")
    if dec and inc: kinds.add("TRANSFER")
    return kinds, dec, inc

if __name__ == "__main__":
    stats = collections.Counter(); hits = []
    bidir = []
    for b1, b2, b3 in itertools.product(range(len(pool)), repeat=3):
        for R in Rs:
            trs = family(b1, b2, b3, R)
            if not trs: continue
            decs, incs = set(), set()
            for c, tr in trs:
                kinds, dec, inc = classify(tr)
                for kd in kinds: stats[kd] += 1
                decs |= set(dec); incs |= set(inc)
                if "TRANSFER" in kinds and len(hits) < 10:
                    hits.append((show(pool[b1]), show(pool[b2]), show(pool[b3]), show(R), c, tr))
            if decs & incs and len(bidir) < 10:
                bidir.append((show(pool[b1]), show(pool[b2]), show(pool[b3]), show(R), sorted(decs & incs)))
    print("transition kinds over all 3-slot families:", dict(stats))
    print("TRANSFER transitions:", len(hits))
    for h in hits: print("   ", h)
    print("families with a counter both incremented and decremented:", len(bidir))
    for b in bidir: print("   ", b)
