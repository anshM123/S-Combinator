"""Agent U round 6 (b): head-style sawtooth. Family X = S S # S over base B0 (both counters). Template
T(i, n, k) = X_i . S^n . X_k . S at the front over opaque tape. Reports every recurrence (symbolic i, k; concrete n)."""
import sys, collections
from agent_u_ctxnest import run, isC, spine
from symb import trees, show
SSxS = ((("S", "S"), "#"), "S")
def node(i, n, k):
    t = i
    for _ in range(n): t = (t, "S")
    return ((t, k), "S")
def stop(K, br, steps):
    h, a = spine(K[0])
    if not isC(h) or len(a) < 2 or a[-1] != "S" or not isC(a[-2]): return None
    if any(x != "S" for x in a[:-2]): return None
    return (h[2:], len(a) - 2, a[-2][2:])
if __name__ == "__main__":
    MAXB = int(sys.argv[1]); NMAX = int(sys.argv[2])
    cnt = collections.Counter(); re = []
    for nb in range(1, MAXB + 1):
        for B0 in trees(nb):
            fams = [(SSxS, B0)]
            for n in range(1, NMAX + 1):
                out = run([node(("C", 0, "i", 0), n, ("C", 0, "k", 0)), "w1", "w2"], fams, stop, maxsteps=120, cap=5)
                for o in out:
                    if isinstance(o[1], tuple):
                        z = o[0].get("i") == ("eq", 0)
                        cnt[("i=0" if z else "i>=1", o[1][0], o[1][1] - n, o[1][2])] += 1
                        if z: re.append((show(B0), n, o[0], o[1], o[2]))
    for k, v in cnt.most_common(20): print(v, k)
    print("re-entries from i = 0:", len(re))
    for r in re[:15]: print(r)
