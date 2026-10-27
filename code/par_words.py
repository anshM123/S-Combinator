"""Structure of the parallel (ReplaceAll) opcode word of one term (main agent, 2026-10-26).
One term per process, so memory is released between terms (par_vs_head.py ran all terms in one process and its memory
grew to 5.5 GB over 14 terms although every term was capped, E95). Prints the reachable DAG size of the current term every
STRIDE passes, the full parallel word (spine length of the element opened at each pass) and the head word, and the loop
prover's cycle candidates for both words (block structure and marker structure).
Usage: python par_words.py TERM PASSES CAP [STRIDE]"""
import sys
sys.setrecursionlimit(1000000)
import hc
import loop_prover as lp
from symb import parse
from par_vs_head import capped_pass, head_ops, Overflow, reset

def dag_size(t):
    seen = set(); todo = [t]
    while todo:
        x = todo.pop()
        if x <= 0 or x in seen: continue
        seen.add(x); todo.append(hc.L[x]); todo.append(hc.R[x])
    return len(seen)

def compact(t):
    """rebuild the node table with only the nodes reachable from t (returns the new id of t)"""
    order = []; seen = set(); todo = [(t, False)]
    while todo:
        x, done = todo.pop()
        if x <= 0: continue
        if done: order.append(x); continue
        if x in seen: continue
        seen.add(x); todo.append((x, True)); todo.append((hc.R[x], False)); todo.append((hc.L[x], False))
    Lo, Ro = list(hc.L), list(hc.R); new = {}
    reset()
    for x in order:
        l, r = Lo[x], Ro[x]
        new[x] = hc.app(new.get(l, l) if l > 0 else l, new.get(r, r) if r > 0 else r)
    return new[t] if t > 0 else t

def par_run(src, N, CAP, stride):
    t = hc.from_tuple(parse(src)); ops = []; sizes = []; why = "done"
    for n in range(N):
        args, h = hc.spine(t)
        if len(args) < 3: why = "hnf"; break
        ops.append(len(hc.spine(args[0])[0]))
        if n % stride == 0: sizes.append((n, dag_size(t)))
        if len(hc.L) > CAP // 2: t = compact(t)
        try:
            t = capped_pass(CAP)(t)
        except Overflow:
            why = "cap"; break
    return ops, sizes, why

def cycles(w):
    out = []
    try:
        for B, q, starts in lp.find_cycles(w)[:3]:
            out.append(f"block {B} x{q}, {len(starts)} cycles, starts {[s for s, n in starts[:6]]}")
    except Exception as e:
        out.append(f"block search failed: {type(e).__name__}")
    for c, q, starts in lp.find_cycles_marker(w)[:2]:
        out.append(f"marker {c!r} q={q}, starts {[s for s, n in starts[:8]]}")
    return out or ["no cycle candidate"]

if __name__ == "__main__":
    src, N, CAP = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    stride = int(sys.argv[4]) if len(sys.argv) > 4 else 10
    reset(); h = head_ops(src, max(N, 3000))
    reset(); p, sizes, why = par_run(src, N, CAP, stride)
    hw, pw = lp.opword(h), lp.opword(p)
    m = min(len(hw), len(pw)); agree = 0
    while agree < m and hw[agree] == pw[agree]: agree += 1
    print(f"{src}: {len(p)} passes ({why}), agrees with the head word for {agree}")
    print("DAG size by pass: " + " ".join(f"{n}:{s}" for n, s in sizes))
    print(f"par word: {pw}")
    print(f"head word (first {len(pw)}): {hw[:len(pw)]}")
    print("par cycles: " + " | ".join(cycles(pw)))
    print("head cycles (first 3000 steps): " + " | ".join(cycles(hw[:3000])))
