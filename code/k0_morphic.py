"""Check the conjectured recursion for the opcode word of K0 = S(SS)S(S(S(SSS)))S (main agent):
a = 1120421120, b_0 = 12·a, b_{k+1} = 12·b_k·42·b_k, W_k = b_k·22·b_k, word = 10111204120211202211203·W_0·3·W_1·3·W_2·3…"""
import sys
sys.setrecursionlimit(1000000)
from symb import parse
import hc
N = int(sys.argv[1])
args, h = hc.spine(hc.from_tuple(parse("S(SS)S(S(S(SSS)))S"))); stk = args[::-1]; ops = []
for n in range(N):
    a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(len(ch))
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
real = "".join(map(str, ops))
a = "1120421120"; b = "12" + a; pred = "10111204120211202211203"
while len(pred) < N:
    pred += b + "22" + b + "3"; b = "12" + b + "42" + b
pred = pred[:N]
bad = next((i for i in range(N) if pred[i] != real[i]), None)
print(f"K0 opcode word, first {N} steps: prediction {'matches exactly' if bad is None else 'differs at step %d' % bad}")
