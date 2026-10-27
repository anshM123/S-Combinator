"""Exact-recurrence prover for eventually periodic head runs (main agent).
Criterion (rigorous): at a checkpoint n1 the stack is A ++ B where A is never popped during [n1, n2); if at n2 the top of the
stack equals B exactly, then by determinism the run from n2 replays the run from n1 forever (it never reaches below B),
so the head run is periodic from n1 with period n2 - n1 (its opcode word is eventually periodic, hence morphic).
Usage: python periodic_prover.py FILE_OF_TERMS [LIMIT]  or  python periodic_prover.py -t TERM..."""
import sys, collections
sys.setrecursionlimit(1000000)
from symb import parse
import hc
CHECKPOINTS = (200, 1000, 4000, 12000)
WINDOW = 25000
def periodic(src):
    start = len(hc.L)
    args, h = hc.spine(hc.from_tuple(parse(src))); stk = args[::-1]
    pending = []                       # [n1, S1 snapshot, m]
    for n in range(CHECKPOINTS[-1] + WINDOW):
        if len(stk) < 3: return ("hnf", n)
        if n in CHECKPOINTS: pending.append([n, list(stk), len(stk) - 3])
        for p in pending:
            n1, S1, m = p
            if n > n1 and stk[-1] == S1[-1]:
                k = len(S1) - m
                if len(stk) >= k and stk[len(stk) - k:] == S1[m:]:
                    return ("periodic", n1, n - n1, k)
            if n >= n1 + WINDOW: continue
            p[2] = min(p[2], len(stk) - 3)
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a)
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
        if len(hc.L) - start > 2_000_000: return ("memory", n)
    return ("not found",)
if __name__ == "__main__":
    if sys.argv[1] == "-t":
        for src in sys.argv[2:]: print(src, periodic(src))
    else:
        terms = [l.strip() for l in open(sys.argv[1], encoding="utf-8") if l.strip()]
        lim = int(sys.argv[2]) if len(sys.argv) > 2 else len(terms)
        st = collections.Counter(); examples = collections.defaultdict(list)
        for i, src in enumerate(terms[:lim]):
            r = periodic(src); st[r[0]] += 1
            if len(examples[r[0]]) < 5: examples[r[0]].append((src, r[1:]))
            if (i + 1) % 1000 == 0: print(f"  {i + 1}: {dict(st)}", flush=True)
        print(dict(st))
        for k, v in examples.items(): print(f"  {k}: {v}")
