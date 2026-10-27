"""Random search for k-ary counters in head runs (main agent).
Sample hnf-free random S-terms (NMIN..NMAX leaves; M35 class without hnf), run STEPS head steps, and for each opcode look
at the gaps between its occurrences (after the first third): if some >= 4 gap values form an arithmetic progression
whose frequencies fall by a common ratio ~ 1/b (b = 2..6), report a base-b ruler law.
Usage: python rand_radix.py SAMPLES NMIN NMAX STEPS SEED OUT
"""
import sys, random, collections
sys.setrecursionlimit(1000000)
from symb import show
from lo_bt import cls, MF
from sm_check import rand_term

def spine(t):
    a = []
    while isinstance(t, tuple): a.append(t[1]); t = t[0]
    a.reverse(); return a

def opseq(t, steps):
    stk = spine(t)[::-1]; out = []
    for _ in range(steps):
        if len(stk) < 3: return None
        a = stk.pop(); bb = stk.pop(); cc = stk.pop()
        args = spine(a); out.append(len(args))
        stk.append((bb, cc)); stk.append(cc); stk.extend(reversed(args))
    return out

def radix(seq):
    best = None
    s0 = len(seq) // 3
    for op in set(seq[s0:]):
        pos = [i for i in range(s0, len(seq)) if seq[i] == op]
        if len(pos) < 60: continue
        g = [b - a for a, b in zip(pos, pos[1:])]
        cnt = collections.Counter(g)
        vals = sorted(cnt)
        for i, v0 in enumerate(vals):
            for v1 in vals[i + 1:]:
                d = v1 - v0
                chain = [v0]
                while chain[-1] + d in cnt: chain.append(chain[-1] + d)
                if len(chain) < 4: continue
                fr = [cnt[v] for v in chain]
                if fr[0] < 30: continue
                rs = [fr[j + 1] / fr[j] for j in range(len(fr) - 1) if fr[j] >= 8]
                if len(rs) < 2: continue
                r = sum(rs) / len(rs)
                if r <= 0: continue
                b = round(1 / r)
                if 2 <= b <= 6 and all(0.75 / b <= x <= 1.33 / b for x in rs):
                    cand = (b, op, chain[:6], fr[:6])
                    if best is None or len(chain) > len(best[2]): best = cand
    return best

if __name__ == "__main__":
    N, NMIN, NMAX, STEPS, SEED, OUT = (int(x) for x in sys.argv[1:6]) , None, None, None, None, sys.argv[6]
    N, NMIN, NMAX, STEPS, SEED = (int(x) for x in sys.argv[1:6])
    rng = random.Random(SEED)
    kinds = collections.Counter(); seen = set(); tries = 0
    with open(OUT, "w", encoding="utf-8") as f:
        while sum(kinds.values()) < N and tries < 200 * N:
            tries += 1
            t = rand_term(rng.randint(NMIN, NMAX), rng)
            if MF[cls(t)] or t in seen: continue
            seen.add(t)
            seq = opseq(t, STEPS)
            if seq is None: kinds["hnf?"] += 1; continue
            r = radix(seq)
            key = f"base {r[0]}" if r else "none"
            kinds[key] += 1
            if r: f.write(f"base {r[0]}\top {r[1]}\tgaps {r[2]}\tfreq {r[3]}\t{show(t)}\n"); f.flush()
        f.write(f"summary: {dict(kinds)} (tries {tries})\n")
    print(dict(kinds))
