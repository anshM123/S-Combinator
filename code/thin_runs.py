"""Thin head runs (main agent, 2026-10-26): runs in which the second list element has spine length <= 1 at every step
(S or S z). Unique-redex runs (Theorems UR-R, UR-C) are the thin runs whose list elements are normal forms; here elements
may contain redexes, so opened elements can have spine >= 3. This enumerates all terms with up to NMAX leaves whose head
run is thin for N steps (and never reaches a head normal form), and reports how many are not unique-redex, their largest
opcode, and their run type (loop / call prover classification is left to the provers; here: max opcode and whether the
opcode word looks periodic).
Usage: python thin_runs.py NMAX N [NMIN]"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from li_explore import has_redex, terms

def thin_run(t, N):
    args, h = hc.spine(t)
    if len(args) < 3: return None
    stk = args[::-1]; ops = []
    for n in range(N):
        if len(stk) < 3: return None
        if len(hc.spine(stk[-2])[0]) >= 2: return None
        a = stk.pop(); bb = stk.pop(); cc = stk.pop(); ch, _ = hc.spine(a); ops.append(len(ch))
        stk.append(hc.app(bb, cc)); stk.append(cc); stk.extend(reversed(ch))
    return ops

if __name__ == "__main__":
    NMAX, N = int(sys.argv[1]), int(sys.argv[2]); NMIN = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    for n in range(NMIN, NMAX + 1):
        found = []
        for t in terms(n):
            ops = thin_run(t, N)
            if ops is None: continue
            args, h = hc.spine(t)
            ur = not any(has_redex(e) for e in args)
            found.append((hc.show(t), ur, max(ops), ops))
        nonur = [f for f in found if not f[1]]
        big = collections.Counter(f[2] for f in nonur)
        print(f"{n} leaves: {len(found)} thin runs of {N} steps, {len(found) - len(nonur)} unique-redex, {len(nonur)} not;"
              f" max opcode among the others: {dict(sorted(big.items()))}", flush=True)
        for s, ur, mx, ops in nonur:
            print(f"   {s:28s} max op {mx}  {''.join(chr(48 + o) for o in ops[:70])}")
