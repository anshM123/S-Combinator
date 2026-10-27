"""Forever-descending one-redex evolutions from small descent lists (main agent, 2026-10-26).
After a descent the evolution restarts from a 3-element active list [p, q, c] of normal forms (the term S p q c), so
the possible steady states can be probed by enumerating such triples directly instead of whole terms. For all normal
forms p, q, c with at most KMAX leaves each, run the one-redex evolution (descents included) for N steps; for those
with at least N/2 descents, test the K-family steady state of code/descent_classify.py from step N/4 on.
Usage: python descent_triples.py KMAX N [KQ KC]  (KQ, KC: separate leaf limits for q and c; default KMAX)"""
import sys, collections
sys.setrecursionlimit(1000000)
import hc
from li_explore import has_redex, terms
from symb import parse
from descent_classify import run, family_index

if __name__ == "__main__":
    KMAX, N = int(sys.argv[1]), int(sys.argv[2])
    KQ = int(sys.argv[3]) if len(sys.argv) > 3 else KMAX; KC = int(sys.argv[4]) if len(sys.argv) > 4 else KMAX
    SS = hc.from_tuple(parse("SS")); K = hc.from_tuple(parse("S(SS)(SS)"))
    nf = lambda k: [t for n in range(1, k + 1) for t in terms(n) if not has_redex(t)]
    P, Q, C = nf(KMAX), nf(KQ), nf(KC)
    print(f"normal forms: p <= {KMAX} leaves {len(P)}, q <= {KQ} {len(Q)}, c <= {KC} {len(C)}; {len(P) * len(Q) * len(C)} triples", flush=True)
    total = forever = fit = 0; misfit = []
    for p in P:
        for q in Q:
            for c in C:
                total += 1
                t = hc.app(hc.app(hc.app(0, p), q), c)
                lists = run(t, N)
                if lists is None or len(lists) < N // 2: continue
                forever += 1; ok = True
                for step, L in lists:
                    if step < N // 4: continue
                    a, b, cc = L
                    nc = family_index(cc, SS, K)
                    if nc is None: ok = False
                    elif a == SS and b == SS: pass
                    elif a == 0:
                        nb = family_index(b, SS, K)
                        if nb is None or nb >= nc: ok = False
                    else: ok = False
                    if not ok:
                        misfit.append((hc.show(p), hc.show(q), hc.show(c), step, "[" + ", ".join(hc.show(e)[:50] for e in L) + "]"))
                        break
                if ok: fit += 1
    print(f"triples: {total}; forever-descending: {forever}; K-family steady state: {fit}; other: {len(misfit)}")
    for m in misfit[:20]: print("   other:", m)
