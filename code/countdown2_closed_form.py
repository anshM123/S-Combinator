"""Growing-opcode countdown S(SS)S(S(S(SS(SS))S))S: test the closed form of the widest element at each epoch."""
import sys
sys.setrecursionlimit(1000000)
sys.path.insert(0, r"C:\Users\anshm\Downloads\money problems\code")
import hc
from symb import parse
S = 0
def ap(*xs):
    r = xs[0]
    for x in xs[1:]: r = hc.app(r, x)
    return r
src = "S(SS)S(S(S(SS(SS))S))S"
t = hc.from_tuple(parse(src)); args, h = hc.spine(t); stk = args[::-1]
mx = 3; widest = []
for n in range(int(sys.argv[1])):
    a = stk[-1]; ch, _ = hc.spine(a)
    if len(ch) > mx: mx = len(ch); widest.append((n, a, stk[::-1][:4]))
    a = stk.pop(); bb = stk.pop(); cc = stk.pop()
    stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
# a_0 from the first widest element of spine 5 (m = 3?): read a_k off the spines and test the recursion
def F(x): return ap(S, S, ap(S, x), ap(S, ap(S, x)))
ok_all = True
for n, E, top in widest[1:]:
    sp = hc.spine(E)[0]; L = len(sp)            # L = m + 2? spine: a_{m-1}, b_{m-1}, a_{m+1}, f_m..f_0  -> L = 3 + (m+1)
    m = L - 4
    am1, bm1, ap1 = sp[0], sp[1], sp[2]
    frames = sp[3:]                               # f_m, ..., f_0
    ok = (bm1 == ap(S, ap(S, am1))) and (ap1 == F(F(am1)))
    # frames: f_k = S a_k b_k (prefix of E up to f_{k+1})
    ak = {m - 1: am1}
    for k in range(m - 2, -1, -1):
        pass
    for i, f in enumerate(frames):
        k = m - i
        fs = hc.spine(f)[0]
        prefix = ap(S, *sp[:3 + i])
        ok_f = len(fs) == 3 and fs[1] == ap(S, ap(S, fs[0])) and fs[2] == prefix
        ok = ok and ok_f
        if k >= 1 and i + 1 < len(frames):
            nxt = hc.spine(frames[i + 1])[0][0]
            ok = ok and (fs[0] == F(nxt))
    print(f"step {n}: spine {L}, m = {m}: closed form holds: {ok}")
    ok_all &= ok
print("ALL:", ok_all)
