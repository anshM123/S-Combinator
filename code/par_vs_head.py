"""Parallel (ReplaceAll) evaluation versus the head run, memory-safe (main agent, 2026-10-26).
For each term: the head run's opcode word, and for the parallel run the spine length of the element opened at each pass
(Lemma PH: one head step per pass, every element below the first three rewritten). Reports how long the two words agree.
The node table is capped INSIDE the pass (an earlier version checked only between passes and reached 9.8 GB, E94); a term
whose parallel run exceeds the cap is reported with the passes completed so far. Writes its PID to ../data/par_vs_head.pid.
Usage: python par_vs_head.py PASSES CAP [NTERMS]"""
import sys, os
sys.setrecursionlimit(1000000)
import hc
from symb import parse

class Overflow(Exception):
    pass

def capped_pass(CAP):
    memo = {}
    def step(t):
        if t <= 0: return t
        r = memo.get(t)
        if r is not None: return r
        if len(hc.L) > CAP: raise Overflow()
        f, z = hc.L[t], hc.R[t]
        if f > 0 and hc.L[f] > 0 and hc.L[hc.L[f]] == 0:          # t = S x y z: contract, do not enter x, y, z
            x, y = hc.R[hc.L[f]], hc.R[f]
            r = hc.app(hc.app(x, z), hc.app(y, z))
        else:
            r = hc.app(step(f), step(z))
        memo[t] = r; return r
    return step

def head_ops(src, N):
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]; ops = []
    for n in range(N):
        if len(stk) < 3: break
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(len(ch))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return ops

def par_ops(src, N, CAP):
    t = hc.from_tuple(parse(src)); ops = []
    for n in range(N):
        args, h = hc.spine(t)
        if len(args) < 3: return ops, "hnf"
        ops.append(len(hc.spine(args[0])[0]))
        try:
            t = capped_pass(CAP)(t)
        except Overflow:
            return ops, "cap"
    return ops, "done"

def reset():
    hc.L[:] = [None]; hc.R[:] = [None]; hc.TAB.clear()

if __name__ == "__main__":
    open("../data/par_vs_head.pid", "w").write(str(os.getpid()))
    N, CAP = int(sys.argv[1]), int(sys.argv[2])
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    rows = [l.rstrip("\n").split("\t") for l in open("../data/sample_union_150.tsv", encoding="utf-8") if l.strip()]
    terms = [r[0] for r in rows if r[1] == "loop_prover.py"][:K]
    for src in terms:
        reset(); h_ = head_ops(src, N)
        reset(); p_, why = par_ops(src, N, CAP)
        m = min(len(h_), len(p_)); agree = 0
        while agree < m and h_[agree] == p_[agree]: agree += 1
        print(f"{src:30s} agree {agree:4d}/{m:4d} ({why}) | head {''.join(chr(48 + x) for x in h_[:36])} | par {''.join(chr(48 + x) for x in p_[:36])}",
              flush=True)
