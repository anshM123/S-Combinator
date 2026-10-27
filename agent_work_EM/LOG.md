# agent_work_EM LOG (NON-UNIVERSALITY / Conjecture EM agent, 2026-10-27)

Brief (coordinator): prove Conjecture EM for leftmost walks from L36-flag-0 terms (or as much as possible):
every infinite leftmost walk is eventually monotone (eventually >= 3 arguments and no child = last argument).
Remaining failure modes after agent_work_U: (a') jump-free, returns infinitely often to nodes q.S with
infinitely many T3/T4 return steps; (b) depth -> infinity with infinitely many pops/returns; (c) infinitely many jumps.
Labels: PROVED / MACHINE-CHECKED / COMPUTATIONALLY CERTIFIED / EXPERIMENTALLY SUPPORTED / CONJECTURAL / REFUTED.
All files of this agent live in agent_work_EM/ (lean/, wip/, scripts).  Base Lean file: agent_work_EM/lean/EMBase.lean
= verbatim copy of agent_work_U/lean/FiniteHalfGen.lean (6,146 lines).

## 10:18 EDT start (`date`)
* Read agent_work_U/LOG.md (FINAL SUMMARY, 04:04-10:12 entries), the theorem map, SA3/SA4 statements.
* Plan: (1) case (a'): classify chains of return steps T1-T4 (the return multipliers q_r form a RIGHTMOST walk,
  q_(r+1) = snd H(q_r)); (2) then (b), (c).

## 10:30 EDT — PROVED (paper; Lean in progress): case (a') is impossible — typed return chains end in T2
Setting (SA4.return_types_S): return multipliers Q k with Reach (args (Q k)) [X k, Q (k+1)] (H(Q k) = S (X k) (Q (k+1)))
and every X k TYPED: T1 X = SS, T2 R(X, y) (H(X) = S S y), T3 X = S(SS), T4 (X has >= 2 args, H(X.S) = S (SS) c1).
Key observation: for a node Q with >= 3 args, final_app gives Q (k+1) = b.(X k): the NEXT multiplier's last argument
is the current first component X k.  Lemmas (all elementary from final_app, reach_stuck, reach_det, OM.cinv2_reach):
 (L4) T4 shape: X = S x' S (exactly two args, last S) [cinv2: the final [SS, c1] = [c.w, b(c.w)] forces c = w = S,
      first wrap, H(X) = S x' S; a >= 3-arg head run never ends with second component S (final_app)].
 (L3) a typed term is never a chain element followed by a typed step: SS, S(SS) have 1 arg; T2: H = S S y gives
      X = S (untyped); T4: S x' S gives next multiplier S (0 args).
 (Lb) once some Q k has >= 3 args, all later do: a 2-arg Q (k+1) = S p (X k) has next multiplier X k, typed (L3).
 (L1) step from Q (k+1) = P.z (z = X k, P with >= 2 args): R-step (X (k+1) = z, R(P, P'), next P'.z) or wrap
      (X (k+1) = c.w with size w >= size z: cinv2 + OM.wh_size).
 (L2) a typed wrap c.w with size w >= size z, z typed (so z /= S): c.w = S(SS) with z = SS, or c = SS (T2).
      [SS = c.w needs w = S; T4 needs w = S (L4); T2 with c >= 2 args needs w = S (R_strip); c = S p needs p = S.]
Proof: sizes drop along 2-arg steps, so some Q k1 has >= 3 args (Lb: then all later).  T2 is absorbing (R-steps keep
X; a wrap from z /= SS is T2 by L2; SS is not T2).  If infinitely many X k were not T2, then none after k1 is, so by L2
every wrap is SS -> S(SS), at most one; afterwards X is constant and every step is an R-step R(P_k, P_(k+1)) — an
infinite R-chain, impossible (C.no_R_chain).  Hence eventually every return step is T2, and SA4.caseA_needs_T34
(flag 0) gives a contradiction.  NO flag hypothesis is needed for 'eventually T2'.
* COMPUTATIONALLY CERTIFIED cross-check (tchain_check.py 11 300): all typed chains from closed q <= 11 leaves satisfy
  (L3), (Lb), (L4), (last argument of Q (k+1) = X k) and the transition rule of (L2); no violation.
  (tchain.py 12 300 -> tchain_12.txt: longest chains with T3/T4 steps are R-countdowns over S(SS) or S a S.)
