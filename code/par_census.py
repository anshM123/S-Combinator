"""Parallel (ReplaceAll) runs of the 150-term census sample with the lazy machine (main agent, 2026-10-26).
Per term: the parallel word for N passes (lazy_par.py), the head word for N steps, how long they agree, the number of
openings where waiting changed the opened element's spine length ('sensitive openings'; zero means the parallel word
equals the head word for these N passes), the largest delay of a sensitive opening, the largest opcode, and the loop
prover's first cycle candidate for the parallel word (block or marker structure).
Usage: python par_census.py N [OUT]"""
import sys, time
sys.setrecursionlimit(1000000)
import lazy_par as lz
import loop_prover as lp
import hc
from symb import parse

def par_stats(src, N, budget=60.0):
    t = lz.from_tuple(parse(src)); stk = [(e, 0) for e in reversed(lz.plain_spine(t))]; ops = []
    sens = 0; maxd = 0; t0 = time.time(); why = "done"
    for now in range(N):
        if len(stk) < 3: why = "hnf"; break
        if now % 1000 == 0 and time.time() - t0 > budget: why = "time"; break
        (x1, b1), (x2, b2), (x3, b3) = stk.pop(), stk.pop(), stk.pop()
        v1, v2, v3 = lz.delay(x1, now - b1), lz.delay(x2, now - b2), lz.delay(x3, now - b3)
        c = lz.spine(v1); ops.append(len(c))
        if now - b1 > 0 and len(c) != len(lz.plain_spine(x1) if lz.KIND[x1] != 2 else lz.spine(x1)):
            sens += 1; maxd = max(maxd, now - b1)
        stk.append((lz.app(v2, v3), now + 1)); stk.append((v3, now + 1))
        stk.extend((e, now + 1) for e in reversed(c))
    return ops, sens, maxd, why

def head_word(src, N):
    hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []
    for n in range(N):
        if len(stk) < 3: break
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(len(ch))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return ops

def first_cycle(w):
    try:
        r = lp.find_cycles(w)
        if r:
            B, q, starts = r[0]; return f"block {B} x{q} ({len(starts)} cycles)"
    except Exception as e:
        return f"block search failed ({type(e).__name__})"
    r = lp.find_cycles_marker(w)
    if r:
        c, q, starts = r[0]; return f"marker {c!r} q={q} ({len(starts)} cycles)"
    return "none"

if __name__ == "__main__":
    N = int(sys.argv[1]); out = sys.argv[2] if len(sys.argv) > 2 else "../data/par_census_150.tsv"
    rows = [l.rstrip("\n").split("\t") for l in open("../data/sample_union_150.tsv", encoding="utf-8") if l.strip()]
    with open(out, "w", encoding="utf-8") as f:
        f.write("term\tprover\tpasses\tend\tagree\tsensitive\tmax_delay\tmax_op\tnodes\tpar_cycle\thead_cycle\n")
        for r in rows:
            src, prover = r[0], r[1]
            lz.reset(); p, sens, maxd, why = par_stats(src, N)
            h = head_word(src, N)
            m = min(len(p), len(h)); agree = 0
            while agree < m and p[agree] == h[agree]: agree += 1
            pw, hw = lp.opword(p), lp.opword(h)
            line = (f"{src}\t{prover}\t{len(p)}\t{why}\t{agree}\t{sens}\t{maxd}\t{max(p) if p else 0}\t{len(lz.KIND)}\t"
                    f"{first_cycle(pw[:30000])}\t{first_cycle(hw[:30000])}")
            f.write(line + "\n"); f.flush(); print(line, flush=True)
