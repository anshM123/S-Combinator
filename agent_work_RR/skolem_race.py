"""Family-level race node for one Skolem equation c = a*b (agent_work_RR).
Clocks (normalisation times under ReplaceAll): B2(a, b) = a-bar b-bar S (ab + 2a - 2, Theorem B2); linear V-bar S (V - 1,
num_S_time); offset z-bar X ((z - 1) + T(X), Lemma A).  Inequalities: (1) c <= ab: L1 = (c+2a-1)-bar S, R1 = B2(a, b);
(2) ab <= c: L2 = B2(a, b), R2 = (c+2a-1)-bar S.  Race node t = S (S Mk (S (z1 L1) (z2 L2))) (S ((z1+1) R1) ((z2+1) R2)).
Pattern: S (S Mk X) (S Y1 Y2) with X normal, Y1 and Y2 not normal.  Claims: (i) Lemma A: n_par(z-bar X) = z - 1 + n_par(X);
(ii) the pattern fires (at the root, never elsewhere) iff max(z1-1+T_L1, z2-1+T_L2) < min(z1+T_R1, z2+T_R2);
(iii) for each (a, b, c): some (z1, z2) fires iff c = ab.  Usage: python skolem_race.py G ZMAX"""
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
def run(t, horizon, MK):
    P = step_fn(); nfm = {}
    def isnf(x):
        if x <= 0: return True
        r = nfm.get(x)
        if r is None:
            f = hc.L[x]
            r = False if (f > 0 and hc.L[f] > 0 and hc.L[hc.L[f]] == 0) else (isnf(hc.L[x]) and isnf(hc.R[x]))
            nfm[x] = r
        return r
    fired = []; other = 0
    for j in range(horizon):
        seen = set(); st = [t]
        while st:
            x = st.pop()
            if x <= 0 or x in seen: continue
            seen.add(x); st.append(hc.L[x]); st.append(hc.R[x])
            f = hc.L[x]
            if f > 0 and hc.L[f] == 0:
                l, rr = hc.R[f], hc.R[x]
                if l > 0 and hc.L[l] > 0 and hc.L[hc.L[l]] == 0 and hc.R[hc.L[l]] == MK:
                    if rr > 0 and hc.L[rr] > 0 and hc.L[hc.L[rr]] == 0:
                        y1, y2 = hc.R[hc.L[rr]], hc.R[rr]
                        if isnf(hc.R[l]) and not isnf(y1) and not isnf(y2):
                            if x == t: fired.append(j)
                            else: other += 1
        u = P(t)
        if u == t: break
        t = u
    return fired, other
G, ZM = int(sys.argv[1]), int(sys.argv[2])
# Lemma A check
okA = 0
for z in range(1, 9):
    for n in range(1, 6):
        for m in range(1, 6):
            reset(); P = step_fn(); t = ap(hnum(z), ap(hnum(n), hnum(m), 0)); k = 0
            while P(t) != t: t = P(t); k += 1
            okA += (k == z - 1 + n * m + 2 * n - 2)
print(f"Lemma A on z-bar (n-bar m-bar S): {okA} of {8*25} agree")
ok = bad = 0; eq_ok = eq_bad = 0
for a in range(1, G + 1):
  for b in range(1, G + 1):
    for c in range(1, G * G + 2):
        anyfire = False
        for z1 in range(1, ZM + 1):
            for z2 in range(1, ZM + 1):
                reset(); MK = nest(12)
                B2 = ap(hnum(a), hnum(b), 0); LIN = ap(hnum(c + 2 * a - 1), 0)
                left = ap(0, ap(hnum(z1), LIN), ap(hnum(z2), B2))
                right = ap(0, ap(hnum(z1 + 1), B2), ap(hnum(z2 + 1), LIN))
                t = ap(0, ap(0, MK, left), right)
                TL1, TR1 = c + 2 * a - 2, a * b + 2 * a - 2
                TL2, TR2 = a * b + 2 * a - 2, c + 2 * a - 2
                lo, hi = max(z1 - 1 + TL1, z2 - 1 + TL2), min(z1 + TR1, z2 + TR2)
                exp = list(range(lo, hi))
                fired, other = run(t, max(lo, hi) + 3, MK)
                if fired == exp and other == 0: ok += 1
                else: bad += 1; print("MISMATCH", a, b, c, z1, z2, fired[:4], exp[:4], other)
                anyfire |= bool(fired)
        if anyfire == (c == a * b): eq_ok += 1
        else: eq_bad += 1; print("EQ MISMATCH", a, b, c)
print(f"race node: {ok} agree, {bad} disagree; equation c = ab detected correctly for {eq_ok} of {eq_ok + eq_bad} triples (z1, z2 <= {ZM})")
