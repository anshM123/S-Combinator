"""Self-reproducing loops inside infinite head runs (the regime where Lemma 9 does not apply).

For a closed term L and opaque data variables x, y (never opened: if a variable reaches head position the run is
'stuck' = the code inspects data), run the head machine on the configuration ch(L) ++ [x, y] and look for a later
configuration [L, D1, ..., Dm] (L itself at the front, as an element, followed by data built from x, y) — a loop whose
one iteration maps the data (x, y) to (D1, ..., Dm). Reported with the iteration length and the data transformation.
Usage: python loopsearch.py MAXLEAVES STEPS
"""
import sys
from symb import trees, show, spine

def run(L, nvars, steps):
    h, args = spine(L)
    K = list(args) + [v for v in ("x", "y", "z")[:nvars]]
    out = []
    for n in range(1, steps + 1):
        if len(K) < 3: return out, "hnf"
        a, b, c = K[0], K[1], K[2]
        ha, aa = spine(a)
        if ha != "S": return out, "stuck"
        K = list(aa) + [c, (b, c)] + K[3:]
        if K and K[0] == L and len(K) >= 2:
            out.append((n, K[1:]))
    return out, "running"

def has_var(t):
    if t in ("x", "y", "z"): return True
    if t == "S": return False
    return has_var(t[0]) or has_var(t[1])

if __name__ == "__main__":
    MAXL, STEPS = int(sys.argv[1]), int(sys.argv[2])
    hits = []
    for n in range(2, MAXL + 1):
        for L in trees(n):
            for nv in (1, 2, 3):
                loops, status = run(L, nv, STEPS)
                for (k, rest) in loops[:1]:
                    if sum(1 for e in rest if has_var(e)) >= 1:
                        hits.append((n, show(L), nv, k, status, [show(e) for e in rest][:5]))
    print(f"loops found: {len(hits)}")
    for h in hits[:30]:
        print("  ", h)
