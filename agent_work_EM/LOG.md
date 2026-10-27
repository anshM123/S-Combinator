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

## 10:38 EDT — MACHINE-CHECKED: case (a') is impossible; Scenario A is impossible for flag 0 (ns CA)
* agent_work_EM/lean/EMA.lean (6,517 lines = lean/EMBase.lean verbatim + namespace CA, ~370 new lines).
  `cd code && python lean_check.py ../agent_work_EM/lean/EMA.lean`: exit 0, 0 errors, 36 theorems checked,
  "LEAN OK: no errors, no sorry"; axioms of every CA theorem: propext, Classical.choice, Quot.sound
  (output saved in agent_work_EM/lean/EMA_check.txt).
* New theorems (C.T = closed S-terms, R x y = H(x) = S S y, FH.LChild = leftmost step, FH.flag = L36 flag):
  - CA.Typed x := x = SS ∨ (∃ y, R x y) ∨ x = S(SS) ∨ (2 <= |args x| ∧ ∃ c1, H(x.S) = S (SS) c1)  [T1-T4].
  - CA.T4_shape: a T4 term has args [x', S].   CA.typed_dead: a typed term followed by a typed step reaches a
    multiplier with < 2 args.   CA.step_types: a typed step from P.z (|args P| >= 2, z typed) is an R-step on P
    keeping z, the wrap SS -> S(SS), or lands on a T2 term.
  - CA.chain_T2 (NO flag hypothesis): if Reach (args (Q k)) [X k, Q (k+1)] and Typed (X k) for all k, then
    ∃ K, ∀ k >= K, ∃ y, R (X k) y.  (Any infinite chain of T1-T4 return steps is eventually T2 only.)
  - CA.no_caseA: u an infinite leftmost walk (∀ j, LChild (u j) (u (j+1))), flag (u 0) = false, jump-free
    (∀ j p τ, u j ≠ S p τ), returning infinitely often to nodes q.S  ⇒  False.  [case (a') CLOSED]
  - CA.depth_to_infinity: u an infinite jump-free leftmost walk with flag (u 0) = false  ⇒
    ∀ d, ∃ N, ∀ j >= N, d < msl (u j)  (right-spine depth -> infinity).  [Scenario A CLOSED for flag 0; uses
    SA3.scenarioA_depth_one + CA.no_caseA + FH.flag_walk]
* Consequence: EM for flag-0 terms can now fail ONLY through (b) an eventually jump-free walk with depth -> infinity
  and infinitely many pops/returns, or (c) infinitely many jumps.
* Cross-check tchain_check.py 12 300 (all q <= 12 leaves): no violation of L3/Lb/L4/transition rule
  (tchain_check_12.txt).

## 10:56 EDT — MACHINE-CHECKED: the remaining gap stated as two conjectures (CA.finite_half_of_J_EMdeep)
* lean/EMA.lean now 6,555 lines; lean_check.py: exit 0, 0 errors, 37 theorems, LEAN OK (lean/EMA_check.txt).
* CA.finite_half_of_J_EMdeep: u infinite leftmost walk, flag (u 0) = false, (J) ∃ N, ∀ j >= N, u j is not a jump
  node S p τ, and (EM_deep) [∀ d, ∃ N, ∀ j >= N, d < msl (u j)] → [∃ j0, ∀ j >= j0, 3 <= |args (u j)| ∧
  u (j+1) ≠ last argument of u j]  ⇒  False.
  So the leftmost finite half for every flag-0 class follows from two conjectures that no longer mention Scenario A:
  (J) every infinite leftmost walk makes finitely many jumps; (EM_deep) an eventually jump-free infinite leftmost walk
  whose right-spine depth tends to infinity is eventually monotone.
* Searches (EXPERIMENTALLY SUPPORTED, no counterexample):
  - late_events.py all 12 1000 15: all 58,786 closed terms with 12 leaves: no flag-0 walk has a pop/jump/return after
    node 15 (38,250 end at S, 20,531 reach a diverging head run); the 5 flag-1 walks run 1,000 nodes with no late event.
  - late_events.py rand 7 600 100 40000 (late_rand_7.txt): 40,000 random gadget compositions: 39,893 flag-0 walks end;
    107 flag-1 walks run 600 nodes, none with a pop/jump/return after node 100.
  - tower_stacks.py 3 400 60: nodes q.Z with Z a word of length <= 3 over {S, SS, S(SS), S(S(SS)), B, M, SSS, S(SS)S}
    on 5 bases, 18 tops (52,650 walks): no flag-0 walk runs 400 nodes; the 198 long walks are flag 1 and have no
    pop/jump/return after node 60.

## 11:02 EDT — ARGUED (sketch, NOT proved): structure of case (b) — the 'deep regime' is a copy-reading recursion
Setting: u jump-free, infinite, depth -> infinity (the only way EM can now fail without jumps).  Facts used:
 (G) READING LEMMA (proof below; Lean in progress): if a node of a jump-free infinite walk is (A.B).σ with B and σ
     non-towers, then A = tw(k+1) with k <= 2 and the child is σ (k = 0, a RETURN), B.σ (k = 1, tail call) or
     σ.(B.σ) (k = 2, Omega-type).  Proof: A /= S (jump); if A had >= 2 args, Lemma Fib over B makes the first hnf
     component of A.B a non-tower Fw, but Lemma Fib over σ needs it to be tw K; so A = S p, H(A.B) = [p, B], p = tw K.
     K = 3 / K >= 4 put a non-tower in the A-slot of the next node.
 (S) strict cut times (last visits to depth <= d) exist for every d; the step there is a Fib step with K in {2, 3}
     and the pushed c0.Z is frozen forever.  Between cut times every pop/return is inside an excursion that ends at
     Fw j (Z, c0.Z), 1 <= j <= K-1 (next cut node).
Picture: once two non-tower levels lie below every node, a top is S (pop), a 'code' term A.(tw n), or a stack COPY
(Omega-type steps put the stack σ itself on top).  By (G) a copy is READ letter by letter: tw1 = SS ends the read with a
return, tw2 = S(SS) skips to the rest, tw3 = S(S(SS)) pushes the rest and reads a copy of the current stack
(recursion); any other letter kills the walk.  Code tops run a TT-chain (finite, SA.no_TT_chain) whose Omega-type
steps CALL a read of the current stack.  Sketch of EM_deep in this picture: letters that stay on the stack are tw2/tw3
(the next permanent CALL reads them first); reading a permanent tw3 re-reads the same tw3 inside the nested copy and
then meets the pushed copy-rest as a letter (death by (G)); with only tw2 letters the first CALL of the fixed base
program never returns (its read re-enters the same base program), so no further return happens: EVENTUALLY MONOTONE.
Gaps in the sketch: the transient part below the regime, K = 3 steps, pops (c0 = S), CALLs with c0 = tw1 inside
returning reads, code tops whose last argument is a tower.  Status: ARGUED only.  Supported by the searches below.

## 11:07 EDT — MACHINE-CHECKED: the reading lemma (DP.gamma_node, DP.gamma_walk) and jump classification (DP.jump_child)
* lean/EMA.lean = EMBase + CA + DP; the version with gamma_node/gamma_walk passed lean_check.py (LEAN OK, 39 theorems);
  DP.jump_child added (checked against the compiled base; full re-check running).
* DP.gamma_node: A /= S, B and σ non-towers, Reach (args ((A.B).σ)) [ch, d]  ⇒  ∃ k, A = tw (k+1) ∧ ch = Fw σ B k.
* DP.gamma_walk: in a jump-free infinite leftmost walk, u t = (A.B).σ with B, σ non-towers  ⇒  ∃ k <= 2,
  A = tw (k+1) ∧ u (t+1) = Fw σ B k  (child σ = RETURN for k = 0, B.σ for k = 1, σ.(B.σ) for k = 2).
  This is the 'gamma' step used inline by SA4/FM, now a reusable theorem: in deep jump-free walks every top whose
  last argument is a non-tower is a READ of a tower letter SS / S(SS) / S(S(SS)).
* DP.jump_child: Q >= 2 args, v non-tower, leftmost child of Q.v a jump node S p τ  ⇒  H(Q) = S (tw K) c0 with
  K = 0: v = S p τ;  K = 1: c0 = S p, τ = v (DISCARD jump: rightmost child of Q is S p, the stack is dropped);
  K = 2: v = S p, τ = c0.v;  K = 3: c0 = S, p = v.  (K >= 4 impossible.)  Over non-tower stacks every jump is a
  discard jump or lands inside the stack — the starting point for case (c).
* EXPERIMENTALLY SUPPORTED: tower_stacks2.py 4 400 60 (tower_stacks2_4.txt): 143,060 walks of q.Z with tops
  q = S (tw K) c (K = 1..3, 7 values of c, + 2 more) and stacks Z = words of length <= 4 over
  {S, SS, S(SS), S(S(SS)), B, M} on 4 bases: no flag-0 walk runs 400 nodes; 249 flag-1 walks run 400 nodes, none with
  a pop/jump/return after node 60.

## 11:14 EDT — MACHINE-CHECKED (vs compiled base; full re-check running): EM_deep reduced to TOWER PUSHES (ns DP)
* DP.tower_letter_frozen / DP.tower_letter_depth: in a jump-free leftmost walk, once tw (k+1).ρ (a tower letter on top
  of ρ) is a spine suffix of a node, it stays a PROPER spine suffix of every later node (tw (k+1).ρ = S (tw k) ρ is a
  jump node), so the depth never comes back down to that level.
* DP.EM_of_TP: u jump-free, infinite, depth -> infinity, and from some T on (TP): every last argument is a non-tower
  and every computed step pushing K >= 2 multipliers has H(q) = S (tw 2) (tw (k+1))  ⇒  u is eventually monotone.
  (Proof: a late pop/return lands at a level d >= depth (u T); an up-crossing of d at p in [T, r) is a K >= 2 step,
  i.e. a tower-letter push at level d, frozen forever — contradiction.  Helpers DP.msl_Fw, DP.upcross.)
* DP.finite_half_of_J_TP: flag (u 0) = false, (J) eventually no jump nodes, (TP_deep) [depth -> infinity ⇒ TP]
  ⇒ False.  So the leftmost finite half for flag 0 follows from J and TP_deep.
* COMPUTATIONALLY / EXPERIMENTALLY SUPPORTED (deep_structure.py 12 400000 1200 -> deep_structure_12.txt; also
  deep_structure.py 11 20000 800): among 400,000 random gadget compositions, 1,002 flag-1 walks of 1,200 nodes are
  deep (depth growing); over the second halves of these walks all 601,200 steps are tail calls (K = 1: 587,167) or
  K = 2 pushes with c0 = S(SS) = tw 2 (14,033) — exactly TP (and the generalized Omega cycle); no pop, jump, return,
  K = 3 or other push.  37 further long flag-1 walks have bounded depth (reload type).

## 11:17 EDT — full re-check: lean/EMA.lean (6,878 lines) LEAN OK (exit 0, 0 errors, no sorry; 44 theorem
##   lines checked by #print axioms, all among propext / Classical.choice / Quot.sound) — output lean/EMA_check.txt
* MACHINE-CHECKED in this file (new today): CA.T4_shape, CA.typed_dead, CA.step_types, CA.chain_T2, CA.no_caseA,
  CA.depth_to_infinity, CA.finite_half_of_J_EMdeep, DP.gamma_node, DP.gamma_walk, DP.jump_child,
  DP.tower_letter_frozen, DP.tower_letter_depth, DP.EM_of_TP, DP.finite_half_of_J_TP.

## 11:17 EDT — ARGUED (not proved): why TP_deep should hold — reads of stack copies
Terminology for a deep jump-free walk (all stacks with two non-tower levels): a LETTER is a right-spine multiplier
of the stack; a K = 2 step q.σ -> σ.(c.σ) pushes the letter c and puts the COPY σ on top; the walk then READS the copy
letter by letter (DP.gamma_walk): tw1 = SS returns (to the level below the copy), tw2 = S(SS) skips, tw3 = S(S(SS))
pushes the rest R of the copy as a letter and reads a copy of the current stack; a letter S gives a jump node, any
other letter with a non-tower rest kills the walk.  Matching (proof of DP.EM_of_TP): every late pop/return lands on a
level created by an up-crossing push, i.e. on c.σ after a K = 2 push of a NON-tower letter c (resumed as code), or on
σ.(c.σ) after a K = 3 push (tower letters are frozen: DP.tower_letter_frozen).
Argued steps toward TP_deep: (1) a frozen tw1 letter ever at the top of the stack forbids any permanent growth above
it (every later K = 2 read returns at once; K = 3 pushes lead to jump nodes), contradicting depth -> infinity;
(2) a frozen non-tower letter can never be read, so every later read must stop above it; temporary letters (pushed by
returning pushes, copy-rests) are non-towers, hence a permanent push happens only when the top letter of the stack is
a frozen tower letter; (3) a permanent tw3 letter is re-read inside its own nested copy and then meets the pushed
copy-rest R (death); so eventually all permanent letters are tw2 and every read passes the whole stack and re-runs
the same base program, whose first push never returns — no further returns (generalized Omega cycle).
Status: ARGUED; the bookkeeping (first permanent push, temporary letters, the base program) is not written out.

## 11:21 EDT — EXPERIMENTALLY SUPPORTED: J and TP on further families (no violation anywhere)
* tower_stacks.py 4 400 60 (tower_stacks_4.txt): 421,290 walks q.Z (Z = words of length <= 4 over
  {S, SS, S(SS), S(S(SS)), B, M, SSS, S(SS)S} on 5 bases, 18 tops): no flag-0 walk runs 400 nodes (296,400 end at S,
  124,158 reach a diverging head run); 732 flag-1 walks run 400 nodes, none with a pop/jump/return after node 60.
* tp_check.py tower 4 1000 (tp_check_tower4.txt): 211 deep flag-1 walks of 1,000 nodes from tower-stack starts:
  second halves = 102,682 tail calls + 2,818 K = 2 pushes of the letter S(SS); no jump, no other push (TP, J hold).
* tp_check.py self 11 1000: the long flag-1 self-applications X X, X X S, S X X, X (S X) (X with 11 leaves) are
  5 bounded-depth (reload-type) walks; no jump in their second halves.

## 11:24 EDT — MACHINE-CHECKED (vs compiled base): no SS letter on top of a stack (DP.no_SS_letter)
* DP.no_SS_letter: in a jump-free infinite leftmost walk no node has the form X.(SS.ρ) with ρ a non-tower.
  Proof (formal): SS.ρ = S S ρ is a jump node, hence frozen (DP.tower_letter_frozen); from any node X'.(SS.ρ) the next
  step is K = 1 (to c.(SS.ρ)), K = 2 (the pushed copy SS.ρ is read by DP.gamma_walk and returns at once to
  c.(SS.ρ)), or K = 0 / K = 3 / K >= 4 / pop / jump, each of which reaches a jump node or contradicts DP.gamma_walk;
  so the walk returns infinitely often to the level directly above the non-tower SS.ρ — impossible by SA.no_scenarioA.
  Consequences for TP_deep: no K = 2 or K = 3 step ever pushes the letter SS (= tw1) over a non-tower stack, and no
  copy put on top by a K = 2 step starts with SS; the remaining TP violations are K = 2 pushes of S or of non-tower
  letters (incl. tw3 reads, which push the rest of the copy) and K = 3 pushes of S(SS).

## 11:28 EDT — MACHINE-CHECKED (vs compiled base): S(SS)-letters are skipped; no push over S(SS)^n.S(S(SS)).B
* DP.Twr2 Y n = S(SS) applied n times on top of Y.  DP.tw2_skips: a node (S(SS)^n Y).X with Y, X non-towers reaches
  Y.X in exactly n steps (reading lemma with k = 1, n times).
* DP.no_tw3_push: in a jump-free infinite walk no K = 2 step (H(q) = S (S(SS)) c) starts at a node q.σ with
  σ = S(SS)^n (S(S(SS)).B), B a non-tower.  (The copy σ is read: n skips, then S(S(SS)) pushes B and puts c.σ on top;
  c = SS is excluded by DP.no_SS_letter, c = S(SS) re-reads σ down to the same S(S(SS)) and then meets the letter B,
  c = S(S(SS)) meets B at once; a non-tower letter is excluded by DP.gamma_walk.)
* Meaning: the copy put on top by any K = 2 step is read by S(SS)-skips until its first other letter, which can only be
  SS (then the read returns; by no_SS_letter such an SS was never pushed — it belongs to the part of the stack present
  from the start) or a letter whose rest is a tower (the BASE of the stack); S(S(SS)), S and non-tower letters are
  impossible there.

## 11:28 EDT — ARGUED (not formalised): TP_deep, and hence EM_deep, by a 'base action' case split
Setting: jump-free, depth -> infinity, stacks eventually two-level non-towers.  Fix a late time T1 with a frozen bottom
segment; every K = 2 copy read skips S(SS)-letters (tw2_skips) and stops at the same place (an initial SS or the base
B*); there the walk performs a FIXED 'base action' — determined by B* alone, after the finite TT-chain of tail calls of
the base program (SA.no_TT_chain): RET (a return), CALL(c*) (a K = 2 push of c*), or K3(c*).
 RET: every K = 2 push is resumed and K = 3 pushes end in a jump node, so nothing is ever pushed permanently —
      contradicts depth -> infinity (strict cut times push permanently).
 CALL(c*): the nested read of the current stack meets the enclosing pushed letter first; SS (no_SS_letter),
      S(S(SS)) (no_tw3_push), S (jump) and non-tower letters (gamma_walk) are impossible, so it is S(SS), the read
      reaches the base again, and the CALL recurses forever: every later K >= 2 push is the CALL of c* = S(SS) — TP.
 K3(c*): c* = S(SS) (SS by no_SS_letter); the next base action meets the copied stack as a letter: death by gamma_walk.
So TP_deep holds, and DP.EM_of_TP gives EM_deep.  Missing for a proof: the formal 'frozen base' bookkeeping (a fixed
B* below every late copy, the base program's determinism), the transient before the first late K = 2 push, and the
'stacks eventually two-level non-towers' hypothesis.  Status: ARGUED.  The machine-checked ingredients are DP.gamma_walk,
DP.tower_letter_frozen, DP.no_SS_letter, DP.tw2_skips, DP.no_tw3_push, DP.EM_of_TP, SA.no_TT_chain, SA.no_scenarioA.

## 11:40 EDT — MACHINE-CHECKED (vs compiled base): a strict cut at a K = 2 step forces a generalized Omega cycle
* New namespace SC (wip/SC_part1-3.lean): SC.fib_next (the Fibonacci child is determined by H(top)), SC.twr2_decomp
  (every term is S(SS)^n Y with Y not S(SS)-headed), SC.BaseChain / SC.base_run / SC.base_exists (the 'base program':
  a finite chain of tail calls b 0 = Y, ..., b i0 followed by a step with K /= 1; it exists when the walk never
  revisits the stack — via no_R2_chain — and it runs identically over every non-tower stack), SC.CycInv / SC.cyc_step /
  SC.cyc_forever (the invariant of the generalized Omega cycle: nodes (S(SS)^k Y).(S(SS)^(m+1) Y), 1 <= k <= m, or
  (b i).(S(SS)^(m+1) Y); it is preserved and every step is monotone).
* SC.cut_monotone: u jump-free infinite leftmost walk; u t = q.σ, σ a non-tower, H(q) = S (S(SS)) c (a K = 2 step),
  and ∀ e, msl (u t) < msl (u (t+1+e)) (t is a strict cut: the depth never comes back to the level of u t)  ⇒
  ∀ e, 3 <= |args (u (t+e))| ∧ u (t+e+1) ≠ last argument of u (t+e).  I.e. from a K = 2 strict cut on, the walk is
  EVENTUALLY MONOTONE (it is a generalized Omega cycle: S(SS)-skips, the base program, a CALL pushing S(SS)).
  This is the formal core of the 11:28 'base action' argument (cases RET / K3 / CALL all handled).

## 11:43 EDT — MACHINE-CHECKED (vs compiled base; full re-check running): case (b) reduced to a tower condition
* SC.copy_monotone: u jump-free infinite, u t1 = σ.(c.σ) (σ a non-tower: a copy on top of the letter c), and the walk
  never visits c.σ from t1 on  ⇒  monotone from t1 on.   (cut_monotone in copy form; no strict-cut hypothesis.)
* SC.no_escape: u s = σ.(σ.Z) (σ, Z non-towers) and the walk never visits σ.Z from s on  ⇒  False.
* SC.K3_monotone: any K = 3 step from q.σ (σ a non-tower, H(q) = S (tw 3) c) in a jump-free infinite walk is followed,
  after finitely many steps, by a monotone walk (c = S(SS); the walk returns to σ.(S(SS).σ); copy_monotone).
* SC.last_le: the last time t >= T with depth <= depth (u T) exists when the depth tends to infinity (a strict cut).
* SC.EM_deep_nt: u jump-free, infinite, depth -> infinity, and stacks eventually non-towers  ⇒  u eventually monotone.
  (Only the stack at ONE strict cut is used: K = 2 -> cut_monotone, K = 3 -> K3_monotone, K >= 4 -> reading lemma.)
* SC.finite_half_of_J_NT: flag (u 0) = false, (J) eventually no jump nodes, (NT) [depth -> infinity ⇒ stacks
  eventually non-towers]  ⇒  False.
* MEANING: Conjecture EM_deep is now PROVED (machine-checked) up to the tower condition NT; together with case (a')
  (CA.no_caseA) the leftmost finite half for flag-0 classes reduces to (J) finitely many jumps and (NT).
  NT fails only in the scenario 'every strict cut sits on a tower stack S(S(...(SS)))' (the frozen limit stack is all S);
  by FM.tower_grow such a stack can never grow by a single S letter at a computed step with a >= 2-argument top.

## 11:46 EDT — full re-check: lean/EMA.lean (7,960 lines) LEAN OK — exit 0, 0 errors, no sorry (lean/EMA_check.txt)
* All CA, DP and SC theorems compile in the single file; axioms only propext / Classical.choice / Quot.sound.
* tower_cut_hunt.py 7 6 600: walks from S x S (tw m) and x.(tw m) (x <= 7 leaves, m <= 6): all 2,364 end — no
  walk showing the tower scenario that (NT) excludes.  (Larger run 9 8 600 started.)

## 11:48 EDT — ARGUED (partial): the tower scenario that (NT) excludes
* If some strict cut of a deep jump-free walk has a non-tower stack, SC.EM_deep_nt's proof applies (it only uses the
  stack at ONE strict cut).  So (NT) can fail only if every late strict cut sits on a tower stack tw m.  Then (argued,
  from FM.tower_grow, final_app and the first-wrap structure of OM.cinv2_reach): the top is S x S, the child pushes S
  at level m+1 (otherwise a frozen non-tower letter makes all later stacks non-towers), the second wrap pushes a
  letter c2 /= S (a non-tower code letter: towers would give jump nodes), the walk later returns to c2.(tw (m+1)),
  and the next strict cut sits on tw (m+1): a 'unary tower counter' that grows by one S per cycle.  Not excluded yet;
  no example found (tower_cut_hunt.py; tp_check.py self 12 1000: the 9 long flag-1 self-applications with 12-leaf X
  are 8 bounded-depth walks and 1 deep generalized-Omega walk, TP holds, no jump).

## 11:51 EDT — tower scenario: structure (ARGUED) and search (EXPERIMENTALLY SUPPORTED)
* tower_cut_hunt.py 9 8 600 (tower_cut_hunt_9.txt): walks from S x S (tw m) and x.(tw m), x <= 9 leaves, m <= 8:
  32,895 end, 1 runs 600 nodes and is deep with non-tower strict cuts; none shows the tower scenario.
* ARGUED refinement of the 11:48 entry: in the tower scenario, consecutive strict cuts at depths d and d+1 sit at
  nodes (S x_d S).(tw (d-1)) and (S x_(d+1) S).(tw d); the returns to depth d+1 in between are R2-steps over the
  tower fuel tw d (the SA3 analysis for tower fuels of height >= 2), and R2-steps into a term whose last argument is not
  S S are syntactic (OM.R2_into), so the second-wrap letter c2 of the strict cut at d is S(SS)^r (S x_(d+1) S) and
  H(x_d . tw (d-1)) = S x2 c2: the code x_(d+1) of the next cycle is read off the rightmost child of x_d.(tw (d-1)).
  A 'unary tower counter' would need a self-reproducing code of this kind; none exists among the terms searched.

## 11:52 EDT — MACHINE-CHECKED (vs compiled base; full re-check running): EM from ONE strict cut (SC.EM_of_cut)
* SC.EM_of_cut: u jump-free infinite, t a strict cut (∀ e, msl (u t) < msl (u (t+1+e))) with ¬ Tower (rpart (u t))
  ⇒ u eventually monotone.  No hypothesis on the depth otherwise.  (EM_deep_nt is the special case found by last_le.)
* SC.finite_half_of_J_NT2: flag (u 0) = false, (J) ∃ N, ∀ j >= N, u j not a jump node, and (NT') for every such N,
  if the depth tends to infinity there is a strict cut t >= N on a non-tower stack  ⇒  False.
* So (NT') — 'a deep jump-free walk has a strict cut on a non-tower stack' — is all that is left of case (b); it fails
  only in the 'unary tower counter' scenario of the 11:48 / 11:51 entries.

## 11:54 EDT — ARGUED (roadmap, not proved): the anatomy of jumps — case (c) / conjecture (J)
* By DP.jump_child, a jump node reached by a computed step over a non-tower stack v comes from one of: K = 1 with
  c0 = S p (DISCARD jump: the target p is the argument of the rightmost child S p of the top; the stack is dropped);
  K = 0 onto a stack level whose letter is S p (a DELAYED discard: the letter S p was pushed as c0 by an earlier K = 2
  step whose copy-read returned); K = 2 with v = S.p (the target is the stack below an S letter, i.e. an OLDER STACK);
  K = 3 with c0 = S (the target is the current stack).  In reading terms, a discard jump from a read top is the
  reading of an S letter of a copy: the walk continues inside the copy-rest (an older stack), dropping the current one.
* So (J) splits into: (J1) finitely many 'code' jumps (targets = arguments of rightmost children S p of tops), and
  (J2) finitely many 'stack' jumps (targets = older stack suffixes; these lower the depth like pops).  Every 'death'
  branch of the jump-free proofs in DP/SC that ends at a jump node is exactly where a walk with jumps continues, so a
  proof of (J) can reuse those case splits.  Evidence: no infinite walk with more than one jump is known; periodic
  walks (the simplest way to jump infinitely often) do not occur among all closed terms with <= 12 leaves
  (periodic_hunt.py, see below).

## FINAL (EM agent) — draft written 11:49 EDT (to be refreshed before 15:00)
**Bottom line.  Case (a') of Conjecture EM is CLOSED and case (b) is closed up to one narrow tower condition, both
MACHINE-CHECKED.  For every L36-flag-0 term, the leftmost Böhm path is finite provided (J) the walk makes only finitely
many jumps and (NT) a deep walk eventually has non-tower stacks (SC.finite_half_of_J_NT).  Scenario A (depth bounded
infinitely often) needs no conjecture any more (CA.depth_to_infinity), and EM_deep — every jump-free infinite walk with
depth -> infinity is eventually monotone — is proved for walks with one strict cut on a non-tower stack
(SC.EM_deep_nt).  The challenge is NOT solved; (J) and (NT) are open; no counterexample was found.**
MACHINE-CHECKED: agent_work_EM/lean/EMA.lean (7,960 lines = agent_work_U/lean/FiniteHalfGen.lean verbatim + new
namespaces CA, DP, SC); `cd code && python lean_check.py ../agent_work_EM/lean/EMA.lean`: exit 0, 0 errors,
59 theorems checked, "LEAN OK: no errors, no sorry", axioms only propext / Classical.choice / Quot.sound (saved in
agent_work_EM/lean/EMA_check.txt).  Notation: u : Nat → C.T an infinite leftmost walk (∀ j, FH.LChild (u j) (u (j+1))),
'jump-free' = ∀ j p τ, u j ≠ S p τ, flag = FH.flag (L36), msl = right-spine depth, R x y = H(x) = S S y.
 Case (a') [ns CA]:
 * CA.chain_T2 (no flag): Reach (args (Q k)) [X k, Q (k+1)] ∧ Typed (X k) for all k ⇒ eventually ∃ y, R (X k) y.
   (Typed = T1 SS / T2 / T3 S(SS) / T4 of SA4.return_types_S; helpers CA.T4_shape, CA.typed_dead, CA.step_types.)
 * CA.no_caseA: flag (u 0) = false, jump-free, returns to nodes q.S infinitely often ⇒ False.
 * CA.depth_to_infinity: flag (u 0) = false, jump-free ⇒ ∀ d, ∃ N, ∀ j >= N, d < msl (u j).
 * CA.finite_half_of_J_EMdeep: flag 0 + (J) + [depth -> ∞ ⇒ eventually monotone] ⇒ False.
 Deep walks [ns DP]:
 * DP.gamma_node / DP.gamma_walk (reading lemma): jump-free, u t = (A.B).σ, B, σ non-towers ⇒ ∃ k <= 2,
   A = tw (k+1) ∧ u (t+1) = Fw σ B k.
 * DP.jump_child: Q >= 2 args, v non-tower, leftmost child of Q.v is S p τ ⇒ H(Q) = S (tw K) c0 with K = 0
   (v = S p τ), 1 (c0 = S p, τ = v: discard jump), 2 (v = S p, τ = c0.v) or 3 (c0 = S, p = v).
 * DP.tower_letter_frozen / DP.tower_letter_depth: a stack segment tw (k+1).ρ, once present, stays a proper suffix
   forever and the depth never returns to its level.
 * DP.EM_of_TP, DP.finite_half_of_J_TP: the tower-push reduction (superseded by SC, kept).
 * DP.no_SS_letter: jump-free ⇒ no node X.(SS.ρ) with ρ a non-tower.   DP.tw2_skips: (S(SS)^n Y).X ⇒ Y.X after n
   steps.   DP.no_tw3_push: no K = 2 step from q.(S(SS)^n (S(S(SS)).B)), B non-tower.
 Strict cuts [ns SC]:
 * SC.fib_next, SC.twr2_decomp, SC.BaseChain / base_run / base_exists, SC.CycInv / cyc_step / cyc_forever.
 * SC.cut_monotone: jump-free, u t = q.σ, σ non-tower, H(q) = S (S(SS)) c, ∀ e, msl (u t) < msl (u (t+1+e))
   ⇒ ∀ e, 3 <= |args (u (t+e))| ∧ u (t+e+1) ≠ rpart (u (t+e))  (a generalized Omega cycle from t on).
 * SC.copy_monotone: jump-free, u t1 = σ.(c.σ), σ non-tower, c.σ never visited from t1 on ⇒ monotone from t1.
 * SC.no_escape, SC.K3_monotone (any K = 3 step over a non-tower stack ⇒ monotone from some later time),
   SC.last_le (strict cuts exist when depth -> ∞).
 * SC.EM_deep_nt: jump-free, depth -> ∞, ∃ T, ∀ t >= T, ¬ Tower (rpart (u t)) ⇒ ∃ j0, ∀ j >= j0,
   3 <= |args (u j)| ∧ u (j+1) ≠ rpart (u j).
 * SC.finite_half_of_J_NT: flag (u 0) = false, (J) ∃ N, ∀ j >= N, u j not a jump node, (NT) [depth -> ∞ ⇒
   ∃ T, ∀ t >= T, ¬ Tower (rpart (u t))] ⇒ False.
OPEN: (J) finitely many jumps (case (c)); (NT) the 'unary tower counter' scenario (every late strict cut on a tower
stack S(S(...(SS))); see the 11:48 entry).  Both are EXPERIMENTALLY SUPPORTED only.
