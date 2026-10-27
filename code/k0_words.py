"""Self-similarity of the robust counter K0's opcode word (main agent): segments W_k between consecutive opcode-3 events;
test W_{k+1} = W_k · X_k · W_k (and variants) for short connector words X_k."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
args, h = hc.spine(hc.from_tuple(parse("S(SS)S(S(S(SSS)))S"))); stk = args[::-1]; ops = []
for n in range(140000):
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(len(ch))
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
ev = [i for i, o in enumerate(ops) if o == 3]
W = [ops[ev[i] + 1: ev[i + 1]] for i in range(len(ev) - 1)]
print("event steps:", ev[:12]); print("segment lengths:", [len(w) for w in W])
for k in range(len(W) - 1):
    a, b = W[k], W[k + 1]
    pre = len(a) <= len(b) and b[:len(a)] == a
    suf = len(a) <= len(b) and b[-len(a):] == a
    mid = b[len(a): len(b) - len(a)] if pre and suf else None
    # longest common prefix / suffix
    lcp = next((i for i in range(min(len(a), len(b))) if a[i] != b[i]), min(len(a), len(b)))
    lcs = next((i for i in range(min(len(a), len(b))) if a[-1 - i] != b[-1 - i]), min(len(a), len(b)))
    print(f"k={k}: |W_k|={len(a)}, |W_k+1|={len(b)}; W_k prefix of W_k+1: {pre}; suffix: {suf}; "
          f"connector: {mid if mid is not None and len(mid) < 40 else (None if mid is None else len(mid))}; lcp={lcp}, lcs={lcs}")
