"""Scan head runs of [D_n, J, K, X] (D_n = S^n.S left comb, J, K, X small closed) and record the depths of left combs
appearing at the front (front = S.(S.(...(S.Y))) with Y not of the form S.Z).  Look for comb-depth sequences that
are neither monotone-affine nor periodic, e.g. halving or 3/2 maps."""
import sys, collections
import hm
def comb_depth(t):
    d = 0
    while t > 0 and hm.L[t] == 0:
        d += 1; t = hm.R[t]
    return d
def run_depths(lst_front_first, steps):
    """depths of combs (>= 2) that appear at the front AFTER the initial descent, as maximal new combs:
    record d only when the previous front was not a comb of depth d+1 (i.e. not just a descent step)."""
    st = list(reversed(lst_front_first)); ds = []; prev = -1
    for i in range(steps):
        if len(st) < 3: break
        f = st[-1]
        d = comb_depth(f)
        if d >= 2 and d != prev - 1 and i > 0: ds.append(d)
        prev = d
        if hm.step(st) < 0: break
    return ds
if __name__ == "__main__":
    smax = int(sys.argv[1]); steps = int(sys.argv[2])
    terms = [t for n in range(1, smax + 1) for t in hm.trees(n)]
    combs = {}
    for n in range(1, 13):
        t = 0
        for _ in range(n): t = hm.app(0, t)
        combs[n] = t
    M0 = hm.mark()
    out = []
    for J in terms:
        for K in terms:
            for X in terms[:6]:
                prof = []
                for n in (6, 7, 8, 9):
                    ds = run_depths([combs[n], J, K, X], steps)
                    hm.truncate(M0)
                    # summarise: distinct depth values seen (in order of first appearance)
                    seen = []
                    for d in ds:
                        if d not in seen: seen.append(d)
                    prof.append(tuple(seen[:12]))
                # interesting if some depth sequence is not monotone
                nonmono = any(len(set(p)) >= 3 and any(p[i] > p[i+1] for i in range(len(p)-1)) for p in prof)
                if nonmono: out.append((hm.show(J), hm.show(K), hm.show(X), prof))
    print("nonmonotone:", len(out))
    for o in out[:40]: print(o)
