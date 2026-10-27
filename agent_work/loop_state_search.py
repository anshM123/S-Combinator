"""Loop with an evolving state slot.
Loop element L_k = N(k).s.(H.S); activating L_k.w1.w2... gives body list  args(H) ++ [S, s, L_{k-1}.s, w1, w2, ...].
Model one iteration generically: list = args(H) ++ [S, s, M, t, J1, J2]  with M (= L_{k-1}.s), t (state), J's opaque.
We want the run to get stuck with an M-headed front M.w1.w2... (the loop continues; next state = w1) where w1 is a
proper transformation of t, e.g. c.t, t.c, c.(d.t) with c, d closed (and contains no M, J)."""
import sys, collections
import hm
M = hm.atom("M"); T = hm.atom("t"); J1 = hm.atom("J"); J2 = hm.atom("K")
def atoms_in(t):
    s = set(); stack = [t]
    while stack:
        i = stack.pop()
        if i < 0: s.add(i)
        elif i > 0: stack.append(hm.L[i]); stack.append(hm.R[i])
    return s
def occ(t, a):
    if t == a: return 1
    if t <= 0: return 0
    return occ(hm.L[t], a) + occ(hm.R[t], a)
if __name__ == "__main__":
    hmax = int(sys.argv[1]); smax = int(sys.argv[2])
    Hs = [t for n in range(1, hmax + 1) for t in hm.trees(n)]
    Ss = [t for n in range(1, smax + 1) for t in hm.trees(n)]
    stats = collections.Counter(); hits = []
    for H in Hs:
        aH, hh = hm.spine(H)
        for s in Ss:
            st = [J2, J1, T, M, s, 0] + list(reversed(aH))
            status, k = hm.run(st, 3000)
            if status != "stuck": stats[status] += 1; continue
            f = st[-1]; fa, fh = hm.spine(f)
            if fh != M: stats["front " + hm.show(fh)] += 1; continue
            if not fa: stats["M bare"] += 1; continue
            w1 = fa[0]
            at = atoms_in(w1)
            if w1 == T: stats["w1=t (same state)"] += 1; continue
            if at == {T} and occ(w1, T) == 1:
                stats["w1=f(t) clean"] += 1
                hits.append((hm.show(H), hm.show(s), k, hm.show(w1), hm.show_list(st)))
            else:
                stats["w1 other: " + ("".join(sorted(hm.NAMES[a] for a in at)))] += 1
    print(stats)
    print("hits:", len(hits))
    for h in hits[:60]: print(h)
