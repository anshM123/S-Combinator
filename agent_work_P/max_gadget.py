"""Exact max gadget with flat combs (agent_work_P, 2026-10-27).
D_d := S S ... S (d+3 leaves, the left comb) is a delay: its own run (ReplaceAll or head) reaches the head normal form
S S c at internal time d (each pass consumes one S; the waiting S-combs are normal, so ReplaceAll = head run here).
Gadget M(d, e) := S D_d R D_e Y   (list [D_d, R, D_e, Y]).
Prediction (Lemma PJ, MACHINE-CHECKED): under ReplaceAll D_e waits (ages) while D_d runs, reaches the front at pass
2 + d with age d, and its hnf spine [S, P^max(0,d-e)(comb(e+1))] (= spine(P^max(d,e)(D_e)), Lemma PJ) is laid out at the front at
pass 3 + max(d, e); the opcode (spine
length of the front element, opened at the next pass) at pass 2 + d is 2 + (e - d if e > d else 0).  Under
leftmost-outermost the hnf of D_e is laid out at step 3 + d + e and the opcode at step 2 + d is e + 2.  So ReplaceAll computes max and truncated subtraction (monus) of the two programmed
delays, where leftmost-outermost computes the sum.  Checked here for all 1 <= d, e <= N (direct passes / head steps)."""
import sys
from ptools import *
def comb(n):
    t = 0
    for _ in range(n - 1): t = hc.app(t, 0)
    return t
N = int(sys.argv[1]) if len(sys.argv) > 1 else 20
R, Y = app(0, 0, app(0, 0)), app(0, app(0, 0))     # arbitrary normal fillers SS(SS) and S(SS)
ok = 0; bad = []
for d in range(1, N + 1):
    for e in range(1, N + 1):
        De = comb(e + 3)
        t = build(0, [comb(d + 3), R, De, Y])
        # ReplaceAll: find the pass at which the front segment is the hnf of D_e's own run, and the opcode at pass 3+d
        target_par = None; op_par = None; u = t
        second_par = comb(e + 1)                         # Lemma PJ: content = spine(P^max(d,e)(D_e)) = [S, P^(d-e)(comb(e+1))]
        for _ in range(max(0, d - e)): second_par = P(second_par)
        for n in range(0, 3 + max(d, e) + 3):
            a, h = spine(u)
            if n == 2 + d: op_par = len(spine(a[0])[0])
            # D_e's hnf has spine [S, comb(e+2)]: front two elements S and the comb
            if target_par is None and len(a) >= 2 and a[0] == 0 and a[1] == second_par and n >= 2 + d: target_par = n
            u = P(u)
        target_lo = None; op_lo = None; u = t
        for n in range(0, 3 + d + e + 3):
            a, h = spine(u)
            if n == 2 + d: op_lo = len(spine(a[0])[0])
            if target_lo is None and len(a) >= 2 and a[0] == 0 and a[1] == comb(e + 1) and n >= 2 + d: target_lo = n
            u = head_step(u)
        pred_par = 3 + max(d, e); pred_op = 2 + max(e - d, 0)
        if (target_par, op_par, target_lo, op_lo) == (pred_par, pred_op, 3 + d + e, e + 2): ok += 1
        else: bad.append((d, e, target_par, op_par, target_lo, op_lo))
print(f"max gadget: {ok} of {N * N} pairs (d, e) <= {N} agree with the predictions; mismatches: {bad[:5]}")
