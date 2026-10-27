import sys
import hm, transfer_graph as tg, chain3 as c3, target3 as T3
P, Y, X, Rr, C = c3.P, c3.Y, c3.X, c3.Rr, c3.FROZ[0]
def parse(s):
    toks = [ch for ch in s if ch in "Sp()"]; pos = [0]
    def atom():
        ch = toks[pos[0]]; pos[0] += 1
        if ch == "S": return 0
        if ch == "p": return P
        t = seq(); pos[0] += 1; return t
    def seq():
        t = atom()
        while pos[0] < len(toks) and toks[pos[0]] != ")": t = hm.app(t, atom())
        return t
    return seq()
def pre(t, w):
    while True:
        if t == w: return True
        if t <= 0: return False
        t = hm.L[t]
D2 = parse(sys.argv[1])
o2, V, st2 = T3.phase(D2, 1500)
w = hm.L[V]; b0, c0 = hm.L[w], hm.R[w]; wy = hm.app(w, Y)
print("V =", hm.show(V), " b0 =", hm.show(b0), " c0 =", hm.show(c0))
a0, _ = hm.spine(c0)
T2 = [wy, Y] + list(reversed(a0))
for t in range(60):
    if len(T2) < 3 or hm.head(T2[-1]) != 0: break
    f, b, c = T2[-1], T2[-2], T2[-3]
    flag = ""
    if pre(f, wy): flag = "  <-- (w.y)-prefixed front"
    if hm.app(b, c) == wy: flag = "  <-- re-creates w.y"
    print("  ", hm.show_list(T2, maxn=6)[:170], flag)
    hm.step(T2)
print("  end:", hm.show_list(T2, maxn=6)[:170])
D3 = tg.subst(tg.subst(V, P, C), Y, P)
s3 = [Rr, Y, X, D3]; s, k = hm.run(s3, 2000)
print("phase 3 ends:", s, k, hm.show_list(s3, maxn=5)[:160].replace("p", "p'"))
