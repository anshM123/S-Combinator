"""Race-node family (agent_work_RR): t(n, m, k) = S (S Mk A) B with A = n-bar m-bar S, B = k-bar k-bar S, Mk = the nest
S(S(...(S S))) with 13 leaves (a normal form; marker).  Pattern pi: an occurrence S (S Mk X) Y with X normal and Y not normal.
Theorem B2: n_par(A) = nm + 2n - 2, n_par(B) = k^2 + 2k - 2.  Claim: pi matches exactly at the root, exactly at the
passes j with n_par(A) <= j < n_par(B); so pi ever matches iff nm + 2n < k^2 + 2k.  Checked by scanning every distinct
subterm at every pass (direct passes).  Usage: python race_family.py G"""
import sys
from nf_scan import hc, step_fn, reset, hnum
def ap(*xs):
    t = xs[0]
    for x in xs[1:]: t = hc.app(t, x)
    return t
def nest(n):
    t = 0
    for _ in range(n): t = hc.app(0, t)
    return t
G = int(sys.argv[1]); ok = bad = 0; fired = 0
for n in range(1, G + 1):
  for m in range(1, G + 1):
    for k in range(1, G + 1):
        reset(); P = step_fn(); MK = nest(12)
        A = ap(hnum(n), hnum(m), 0); B = ap(hnum(k), hnum(k), 0)
        t = ap(0, ap(0, MK, A), B)
        nfm = {}
        def isnf(x):
            if x <= 0: return True
            r = nfm.get(x)
            if r is None:
                f = hc.L[x]
                if f > 0 and hc.L[f] > 0 and hc.L[hc.L[f]] == 0: r = False
                else: r = isnf(hc.L[x]) and isnf(hc.R[x])
                nfm[x] = r
            return r
        TA, TB = n * m + 2 * n - 2, k * k + 2 * k - 2
        match_passes = []; nonroot = 0
        for j in range(max(TA, TB) + 2):
            seen = set(); st = [t]
            while st:
                x = st.pop()
                if x <= 0 or x in seen: continue
                seen.add(x); st.append(hc.L[x]); st.append(hc.R[x])
                # pattern: x = app(app(S, app(app(S, MK), X)), Y)
                f = hc.L[x]
                if f > 0 and hc.L[f] == 0:
                    l = hc.R[f]
                    if l > 0 and hc.L[l] > 0 and hc.L[hc.L[l]] == 0 and hc.R[hc.L[l]] == MK:
                        if isnf(hc.R[l]) and not isnf(hc.R[x]):
                            if x == t: match_passes.append(j)
                            else: nonroot += 1
            t = P(t)
        exp = list(range(TA, TB)) if TA < TB else []
        if match_passes == exp and nonroot == 0: ok += 1
        else: bad += 1; print("MISMATCH", n, m, k, match_passes[:5], exp[:5], nonroot)
        if exp: fired += 1
print(f"race family: {ok} agree, {bad} disagree, grid {G}^3; pi fires (nm + 2n < k^2 + 2k) in {fired} cases")
