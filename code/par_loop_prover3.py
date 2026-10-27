"""Parallel loop prover, lazy representation + loops over evolving comb families (main agent, 2026-10-26).
Extends par_loop_prover2.py. There a loop (block lemma A(F(O)) →^L A(O)) is accepted only for a normal comb family,
because the loop variable O is treated as a normal form (no pass changes it). In many parallel runs the comb layers carry
pending passes (sub-terms that keep evolving), so the family is not normal. For such a family the block lemma is checked
again with O and VAR as *general* atoms: aging an element that contains them is then tracked exactly (pending-pass nodes),
so the lemma holds for every instance of O, normal or not, whenever the comparison succeeds (it fails if an element
containing O waits during the block). Usage: python par_loop_prover3.py TERM [TERM ...]"""
import sys
sys.setrecursionlimit(1000000)
import hc
import par_loop_prover2 as p2
import par_loop_prover as plp
import loop_prover as lp
from loop_prover import Fail, JUNKSET

GENERAL = [False]                                      # while True, OPQ and VAR count as arbitrary terms
_nf_gen = {}
def nf_mode(x):
    if not GENERAL[0]: return plp.nf_int(x)
    if x <= 0: return x not in JUNKSET and x not in (lp.OPQ, lp.VAR)
    r = _nf_gen.get(x)
    if r is None:
        args, h = hc.spine(x)
        r = h == 0 and len(args) <= 2 and all(nf_mode(a) for a in args)
        _nf_gen[x] = r
    return r
p2.nf_int = nf_mode                                    # ParEng2.nf looks it up at call time

_block = lp.block_lemma
def recheck(r):
    if r is None or plp.fam_normal(r[3], r[4]): return r
    A, h, b, F, X, L, P = r
    GENERAL[0] = True
    try:
        ok = _block(A, F, L)[0]
    except Fail:
        ok = False
    finally:
        GENERAL[0] = False
    return r if ok else None
def block_ok(A, F, X, Lb):
    """the block lemma A(F(O)) →^Lb A(O): with O a normal atom for a normal family, else with O general"""
    if plp.fam_normal(F, X): return _block(A, F, Lb)
    GENERAL[0] = True
    try:
        return _block(A, F, Lb)
    except Fail:
        return False, None, ()
    finally:
        GENERAL[0] = False

def general_macro_la(eng, cur, hist, Lmax=170, look=(0, 1, 2)):
    """loop_prover.general_macro with lookahead: the window is abstracted with bmin − ℓ, i.e. ℓ comb layers above the
    variable are written out, so a block may read (e.g. by forcing a pending pass) up to ℓ layers below the one it
    peels. A(F(O)) →^Lb A(O) is still a block lemma for every O, and the loop runs n + bmin − ℓ blocks."""
    key = tuple(lp.skel(x) for x in cur[:3])
    for Lb in range(1, min(Lmax, len(hist)) + 1):
        prev = hist[-Lb]
        if tuple(lp.skel(x) for x in prev[:3]) != key: continue
        occ = []; h = 0
        while h < min(len(prev), len(cur)):
            o2 = []
            if not lp.diff(prev[h], cur[h], o2): break
            occ += o2; h += 1
        if h < 3 or not occ or len({o[1:3] for o in occ}) != 1: continue
        F, X = occ[0][1], occ[0][2]; bmin = min(o[3] for o in occ)
        for la in look:
            b0 = bmin - la
            for hh in range(h, 2, -1):
                A = [lp.abstract(prev[i], cur[i], b0) for i in range(hh)]
                if not any(lp.contains(a, lp.VAR) for a in A): break
                ok, sub, P = block_ok(A, F, X, Lb)
                if ok:
                    eng.n0 = max(eng.n0, sub.n0, -b0)
                    return A, hh, b0, F, X, Lb, P
    return None

# The settle check of the aging rule (does an active element reach a normal form within KMAX passes?) must not unfold comb
# tokens: forcing an element whose comb layers keep evolving would otherwise unfold the comb level after level (n0 blows
# up before any loop is found). A settle check that would unfold a token gives up and keeps the pass pending, which is
# exact; the concrete side has no tokens, so a disagreement can only make a comparison fail.
NOUNF = [False]
_spine2 = p2.ParEng2.spine
def spine_nounf(self, a):
    if NOUNF[0] and lp.is_tok(a): raise Fail("settle check would unfold a token")
    return _spine2(self, a)
p2.ParEng2.spine = spine_nounf
_age_active = p2.ParEng2.age_active
def age_active_nounf(self, x, k):
    old = NOUNF[0]; NOUNF[0] = True
    try:
        return _age_active(self, x, k)
    finally:
        NOUNF[0] = old
p2.ParEng2.age_active = age_active_nounf

_sm = plp._sm                                          # loop_prover's own simple macro finder (no normality filter)
def simple_macro(eng, top, L, opq=lp.OPQ, var=lp.VAR): return recheck(_sm(eng, top, L, opq, var))
lp.simple_macro, lp.general_macro = simple_macro, general_macro_la

if __name__ == "__main__":
    for src in sys.argv[1:]:
        try:
            r = p2.prove(src)
        except Fail as e:
            r = {"status": f"failed ({e})"}
        extra = ""
        if r["status"] == "PROVED":
            extra = (f"  (B = {r['B']}, {r['q']} loop(s) per cycle, window {r['window']}, cycle length {r['alpha']}·n + "
                     f"{r['beta']}, n >= {r['n0']}, {r['macros']} macro(s), first cycle {r['first_cycle']}, cross-check "
                     f"{r['crosscheck'][0]}/{r['crosscheck'][1]}, anchor {plp.LAST_DELTA[0][0]}·n + {plp.LAST_DELTA[0][1]})")
        print(f"{src}: parallel run {r['status']}{extra}", flush=True)
