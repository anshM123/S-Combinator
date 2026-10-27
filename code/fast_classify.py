"""Fast head-run classifier and random sample of larger hnf-free terms (main agent).
Same classes as classify2.py (bounded/linear by factor complexity of capped opcodes, single counter by affine-periodic
blocks or gaps, binary counter by ruler law, nested counter), plus 'radix b' (rand_radix.radix, b = 2, 3), computed on a
fast hash-consed run. Usage: python fast_classify.py SAMPLES NMIN NMAX STEPS SEED OUT"""
import sys, random, collections
sys.setrecursionlimit(1000000)
from symb import show
from lo_bt import cls, MF
from sm_check import rand_term
from cxclassify import blocks_of, affine_periodic
from classify2 import ruler_fit, nested_fit
from rand_radix import radix
import hc
def opseq(t, steps):
    args, h = hc.spine(hc.from_tuple(t)); stk = args[::-1]; out = []
    for _ in range(steps):
        if len(stk) < 3: return None
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        out.append(len(ch)); stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return out
def pcx(seq, m): return len({tuple(seq[i:i + m]) for i in range(len(seq) - m + 1)})
def classify(raw):
    seq = [min(x, 3) for x in raw]
    steps = len(seq); s = seq[steps // 3:]
    ps = [pcx(s, m) for m in (8, 16, 32, 64)]
    if ps[-1] <= ps[0] * 1.05 or (ps[3] <= 2.5 * ps[2] and ps[2] <= 2.5 * ps[1]): return "bounded/linear"
    for op in range(4):
        b = blocks_of(seq, op)
        if b and affine_periodic(b): return "single counter"
    gaps = {}
    for op in range(4):
        pos = [i for i, x in enumerate(seq) if x == op]
        g = [b - a for a, b in zip(pos, pos[1:])]; gaps[op] = g
        if len(g) >= 12 and affine_periodic(g + [0]): return "single counter"
    r = radix(raw)
    if r and r[0] in (2, 3): return f"radix {r[0]}"
    for op in range(4):
        if ruler_fit([x for x in gaps[op] if x > 6]): return "radix 2"
    for op in range(4):
        b = blocks_of(seq, op)
        if b and nested_fit(b): return "nested counter"
        if nested_fit([x for x in gaps[op] if x > 6]): return "nested counter"
    return "OTHER"
if __name__ == "__main__":
    N, NMIN, NMAX, STEPS, SEED = (int(x) for x in sys.argv[1:6]); OUT = sys.argv[6]
    rng = random.Random(SEED); kinds = collections.Counter(); seen = set(); tries = 0
    with open(OUT, "w", encoding="utf-8") as f:
        while sum(kinds.values()) < N and tries < 400 * N:
            tries += 1
            t = rand_term(rng.randint(NMIN, NMAX), rng)
            if t in seen or MF[cls(t)]: continue
            seen.add(t)
            raw = opseq(t, STEPS)
            c = "hnf?" if raw is None else classify(raw)
            kinds[c] += 1
            if c in ("OTHER", "nested counter", "radix 3"):
                f.write(f"{c}\t{show(t)}\n"); f.flush()
            if sum(kinds.values()) % 100 == 0: print(f"  {sum(kinds.values())}: {dict(kinds)}", flush=True)
        f.write(f"summary: {dict(kinds)} (tries {tries})\n")
    print(dict(kinds))
