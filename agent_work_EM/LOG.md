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


## 11:59 EDT — MACHINE-CHECKED (vs compiled base; full re-check running): the S-push dichotomy (SC.tower_cut_S)
* SC.tower_cut_S: u jump-free infinite, depth -> infinity, t a strict cut with u t = q.(tw m)  ⇒  either some later
  t' > t is a strict cut with a non-tower stack (then SC.EM_of_cut applies), or q = S x S and the child u (t+1) has
  tw (m+1) as a right-spine suffix (it pushes the letter S onto the tower).  (The letter pushed directly above the
  stack is the second component of H(q), by SA3.wh_c0; if it is not S, it is a frozen non-tower letter.)
* So (NT') fails only if every late strict cut is an S-push node (S x S).(tw m).  ARGUED continuation: the same
  wh_c0 argument at the later visits to depth m+2 shows that the tops met there form a RIGHTMOST walk
  y_1 = snd H(x.(tw m)) -> y_2 = snd H(y_1) -> ... ending at the next S-push top S x' S; a 'tower counter' is a code
  sequence x_m with the rightmost path of snd H(x_m.(tw m)) passing through S x_(m+1) S.  No single counter step
  exists for codes x <= 8 leaves, 2 <= m <= 6 (tower_counter_hunt.py 8 6 400 -> tower_counter_8.txt).

## 12:02 EDT — PROVED (paper; Lean in progress): (NT') holds — the tower counter cannot take a single step
* phi_hunt.py 9 8 200: for all codes x <= 9 leaves and 2 <= m <= 8 the rightmost walk from snd H(x.(tw m)) never
  reaches a node S x' S (0 counter steps among 14,392 cases) — and the reason is structural:
* Argument.  Let t0 be an S-push strict cut, u t0 = (S x S).(tw m), m >= 2 (SC.tower_cut_S).  The head run of
  [x, S, tw m] continues as the run of the virtual node x.(tw m).(tw (m+1)), so by SA3.wh_c0 the child has the suffix
  W = c2.(tw (m+1)) with c2 = snd H(x.(tw m)), and tw m is a right-spine suffix of c2 (final_app + FM.first_suf, or
  c2 = tw m when x = S p).  Invariant after t0: the spine node at depth m+2 is y.(tw (m+1)) with tw m a suffix of y
  (kept by non-jump steps above it; at a visit to depth m+2 the next such y is snd H(y) by SA3.wh_c0, and tw m stays a
  suffix by final_app + first_suf or, for a 2-argument y, because snd H(y) is its last argument).  If the walk never
  returns to depth m+2, W (a non-tower: c2 /= S) is frozen and every later strict cut sits on a non-tower stack.
  Otherwise the LAST visit t1 to depth m+2 is a strict cut on the tower stack tw (m+1) with top y, tw m ⊑ y; by
  SC.tower_cut_S either a later strict cut has a non-tower stack, or y = S x' S — impossible, since tw m (m >= 1) is
  not a suffix of S x' S.  Hence every deep jump-free walk has, after any time N, a strict cut on a non-tower stack.

## 12:04 EDT — MACHINE-CHECKED (vs compiled base; full re-check running): EM_deep, and the finite half from (J) alone
* SC.snd_suf (the second hnf component of Q.z has z as a spine suffix), SC.child_suf (the child of y.Z is Z or has
  the suffix (snd H y).Z), SC.suf_msl_eq, SC.msl_tw.
* SC.NT_holds: u jump-free infinite, depth -> infinity  ⇒  ∀ N, ∃ t >= N, t is a strict cut and rpart (u t) is a
  non-tower.  (The 12:02 paper argument, formalised: the tower counter cannot take one step.)
* **SC.EM_deep: u jump-free infinite, depth -> infinity  ⇒  u eventually monotone** (∃ j0, ∀ j >= j0,
  3 <= |args (u j)| ∧ u (j+1) ≠ rpart (u j)).  No flag hypothesis: Conjecture EM is now a THEOREM for all
  jump-free walks whose depth tends to infinity (case (b) CLOSED).
* **SC.finite_half_of_J: flag (u 0) = false and (J) ∃ N, ∀ j >= N, u j is not a jump node S p τ  ⇒  False.**
  I.e. an infinite leftmost walk from an L36-flag-0 term must make infinitely many jumps.  Together with Proposition
  Q'' (flag 1 ⇒ infinite path): IF Conjecture J holds (every infinite leftmost walk makes only finitely many jumps),
  L36 DECIDES leftmost-path finiteness.  Cases (a') and (b) of EM are closed; only case (c) remains.

## 12:07 EDT — full re-check: lean/EMA.lean (8,480 lines) LEAN OK — exit 0, 0 errors, no sorry, 65 theorems checked,
##   axioms only propext / Classical.choice / Quot.sound (lean/EMA_check.txt).  SC.NT_holds, SC.EM_deep and
##   SC.finite_half_of_J are now MACHINE-CHECKED in the single file.
* Saved search outputs: periodic_rand21.txt (100,000 random gadget compositions, 2,000 nodes: 59,470 diverging head
  runs, 40,248 end at S, 282 run 2,000 nodes; no periodic walk), periodic_all12.txt (all 58,786 terms with 12 leaves:
  no periodic walk), deep_structure_13.txt (1,046 more deep flag-1 walks: 612,955 tail calls + 14,645 K = 2 pushes
  of S(SS), no other step), tower_counter_10.txt (34,590 code/height pairs, x <= 10 leaves: no counter step),
  late_all12.txt, tower_stacks_3.txt.

## 12:10 EDT — roadmap for case (c) / Conjecture J (ARGUED observations, nothing proved)
* Macro view: between two computed nodes w, w' (>= 3 args) the walk takes c = fst H(w) and DESCENDS through first
  arguments of 1- and 2-argument nodes (pops S x -> x, jumps S x y -> x) until a node with >= 3 arguments; J says that
  eventually every descent is empty.  Over a non-tower stack v (Lemma Fib, DP.jump_child) a non-empty descent starts
  from K = 0 onto v = S p τ or S x, K = 1 with c0 = S or S p, K = 2 with v = S p, or K = 3 with c0 = S.
* Jumps into a tower, or into a node whose top letter is a tower letter tw (k+1) (= a jump node S (tw k) R), end the
  path; so in the deep regime 'stack jumps' (targets = older stack suffixes whose top letter is a pushed S(SS)) end
  the walk, and only 'code' jumps (targets p with S p = snd H(top)) can recur.
* A natural first target: eventually periodic walks (the simplest way to jump forever) — none among all closed terms
  with <= 12 leaves or 100,000 random gadget compositions (periodic_hunt.py).  Jump-free periodic walks are already
  impossible (Scenario A ⇒ reload cycle by RC2.reload_classification_full, whose counters grow; EM_deep otherwise).

## FINAL (EM agent) — written 12:08 EDT, refreshed 12:27 EDT

**Bottom line.  Cases (a') and (b) of Conjecture EM are CLOSED, both MACHINE-CHECKED; only case (c) — infinitely many
jumps — remains.  Precisely: (1) every jump-free infinite leftmost walk whose right-spine depth tends to infinity is
eventually monotone (SC.EM_deep, no flag hypothesis); (2) a jump-free infinite leftmost walk from an L36-flag-0 term
has depth tending to infinity (CA.depth_to_infinity; Scenario A closed); (3) hence an infinite leftmost walk from a
flag-0 term must make infinitely many jumps (SC.finite_half_of_J).  So IF Conjecture J holds (every infinite leftmost
walk makes only finitely many jumps, i.e. nodes S p τ), every flag-0 term has a finite leftmost Böhm path, and with
Proposition Q'' (flag 1 ⇒ infinite path) the 36-class model L36 DECIDES leftmost-path finiteness of S-terms.  J is
open (EXPERIMENTALLY SUPPORTED only).  The challenge is NOT solved; no counterexample to anything was found.**

### MACHINE-CHECKED
File: agent_work_EM/lean/EMA.lean (8,480 lines) = agent_work_U/lean/FiniteHalfGen.lean verbatim (6,146 lines) + new
namespaces CA, DP, SC.  Check: `cd code && python lean_check.py ../agent_work_EM/lean/EMA.lean` → exit 0, 0 errors,
65 theorems checked, "LEAN OK: no errors, no sorry", axioms only propext / Classical.choice / Quot.sound (output saved
in agent_work_EM/lean/EMA_check.txt; compile ≈ 2-3 min with ~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean).
Notation: C.T = closed S-terms; u : Nat → C.T with hchild : ∀ j, FH.LChild (u j) (u (j+1)) is an infinite leftmost
walk; jump-free = ∀ j p τ, u j ≠ S p τ; FH.flag = L36 flag; SA2.msl = right-spine depth; SA.rpart = last argument;
H(q) = S a b means Reach (args q) [a, b]; R x y = H(x) = S S y; tw k = S(S(...(S S))) (towers); strict cut at t =
∀ e, msl (u t) < msl (u (t+1+e)).
Headline theorems (line numbers in EMA.lean):
* SC.finite_half_of_J (8454): flag (u 0) = false ∧ (∃ N, ∀ j >= N, ∀ p τ, u j ≠ S p τ) ⇒ False.
* SC.EM_deep (8443): u jump-free ∧ (∀ d, ∃ N, ∀ j >= N, d < msl (u j)) ⇒ ∃ j0, ∀ j >= j0,
  3 <= |args (u j)| ∧ u (j+1) ≠ rpart (u j).   [no flag hypothesis]
* CA.depth_to_infinity (6467): flag (u 0) = false ∧ u jump-free ⇒ ∀ d, ∃ N, ∀ j >= N, d < msl (u j).
* CA.no_caseA (6382): flag (u 0) = false ∧ jump-free ∧ (∀ N, ∃ j >= N, ∃ q, u j = q.S) ⇒ False.   [case (a')]
* CA.chain_T2 (6254): Reach (args (Q k)) [X k, Q (k+1)] ∧ Typed (X k) for all k ⇒ eventually ∃ y, R (X k) y
  (T1-T4 return chains end in T2; no flag).
* SC.NT_holds (8251): u jump-free ∧ depth -> ∞ ⇒ ∀ N, ∃ t >= N, t a strict cut with ¬ Tower (rpart (u t)).
* SC.EM_of_cut (7972): u jump-free, t a strict cut with ¬ Tower (rpart (u t)) ⇒ u eventually monotone.
* SC.cut_monotone (7367): u jump-free, u t = q.σ, σ non-tower, H(q) = S (S(SS)) c, t a strict cut ⇒ monotone from t
  (a generalized Omega cycle).  SC.copy_monotone (7537): u t1 = σ.(c.σ), σ non-tower, c.σ never visited ⇒ monotone
  from t1.  SC.K3_monotone (7811): a K = 3 step over a non-tower stack ⇒ monotone from some later time.
  SC.tower_cut_S (8066): a strict cut on a tower stack is an S-push node (S x S).(tw m) or is followed by a strict cut
  on a non-tower stack.  SC.no_escape, SC.base_exists / base_run / BaseChain, SC.cyc_step / cyc_forever / CycInv,
  SC.fib_next, SC.twr2_decomp, SC.snd_suf, SC.child_suf, SC.last_le.
* Deep-walk lemmas [DP]: DP.gamma_walk (6596; reading lemma: jump-free, u t = (A.B).σ with B, σ non-towers ⇒
  A = tw (k+1), k <= 2, u (t+1) = Fw σ B k), DP.gamma_node, DP.no_SS_letter (6907; no node X.(SS.ρ), ρ non-tower),
  DP.tw2_skips, DP.no_tw3_push (7060), DP.tower_letter_frozen (6693) / tower_letter_depth, DP.jump_child (6646;
  classification of jump nodes over non-tower stacks), DP.EM_of_TP, DP.finite_half_of_J_TP, DP.msl_Fw, DP.upcross.
* Intermediate reductions (superseded but kept): CA.finite_half_of_J_EMdeep (6530), SC.EM_deep_nt,
  SC.finite_half_of_J_NT, SC.finite_half_of_J_NT2.
Unchanged predecessor theorems used: FM.fib_step, FM.finite_half_monotone_all / EM.finite_half_of_EM, SA.no_TT_chain,
SA.no_scenarioA, SA.step_keeps, SA3.scenarioA_depth_one, SA3.wh_c0, SA4.return_types_S, SA4.caseA_needs_T34,
OM.cinv2_reach, C.no_R_chain, C.no_R2_chain, FH.flag_walk.

### Proof architecture (readable)
(a') Return multipliers satisfy H(Q k) = S (X k) (Q (k+1)) with typed X k; the next multiplier's last argument is X k
(final_app), so typed steps propagate: T2 is absorbing, T1/T3/T4 allow only R-steps or the one wrap SS -> S(SS);
infinitely many non-T2 steps would give an infinite R-chain.  Eventually T2 ⇒ fuel-S tail calls ⇒ reload cycle ⇒ flag 1.
(b) Over non-tower stacks every computed step is Fibonacci (Lemma Fib); the reading lemma forces any top whose last
argument is a non-tower to be a tower letter S S / S(SS) / S(S(SS)).  At a strict cut on a non-tower stack the step
pushes K = 2 (or K = 3) multipliers; the copied stack is read letter by letter (S(SS) skips), its first other letter
starts a base program whose final step must be a CALL pushing S(SS) (returns violate the cut; SS and S(S(SS)) letters
are excluded by no_SS_letter / no_tw3_push; K = 3 and K >= 4 die by the reading lemma), and the CALL recurses
forever: a generalized Omega cycle, monotone.  Strict cuts on tower stacks are S-pushes (S x S).(tw m); the tops met
afterwards at depth m+2 all have tw m as a spine suffix, so the next S-push cannot happen and a non-tower strict cut
follows (NT_holds).  Then FM.finite_half_monotone_all (predecessor) excludes flag 0.

### OPEN
* Conjecture J (case (c)): every infinite leftmost walk (or: every infinite leftmost walk from a flag-0 term) makes
  only finitely many jumps.  ARGUED anatomy (LOG 11:54): over non-tower stacks a jump comes from a rightmost child
  S p of a top (discard jump), a delayed discard, an S letter on the stack (target = an older stack) or K = 3 with
  c0 = S; jumps into towers end the path.  No proof.
* Nothing else of EM is open for jump-free walks.

### Numbers and the scripts behind them (all in agent_work_EM/, outputs saved next to them)
* tchain_check.py 12 300 → tchain_check_12.txt: all typed return chains from closed q <= 12 leaves obey the CA lemmas
  (no violation; transitions R 1,564, ->T2 119).  tchain.py 12 300 → tchain_12.txt.
* deep_structure.py 12 400000 1200 → deep_structure_12.txt and 13 400000 1200 → deep_structure_13.txt: 2,048 deep
  flag-1 walks of 1,200 nodes; second halves 1,228,800 steps = 1,200,122 tail calls + 28,678 K = 2 pushes of S(SS);
  no pop, jump, return, K = 3 or other push (the generalized-Omega structure that SC proves).
* tp_check.py tower 4 1000 → tp_check_tower4.txt (211 deep walks, TP holds, no jump); tp_check.py self 10/11/12 1000
  → tp_check_self10/11/12.txt (long flag-1 self-applications: reload or generalized Omega, no jump).
* late_events.py all 12 1000 15 → late_all12.txt (all 58,786 terms with 12 leaves: no pop/jump/return after node 15
  in any walk; 5 flag-1 walks run 1,000 nodes); late_events.py rand 7 600 100 40000 → late_rand_7.txt and
  rand 8 600 100 200000 → late_rand_8.txt (240,000 random gadget compositions in all: every flag-0 walk ends —
  199,459 + 39,893 —, the 648 flag-1 walks run 600 nodes, none with a pop/jump/return after node 100).
* tower_stacks.py 3 / 4 400 60 → tower_stacks_3.txt / tower_stacks_4.txt (52,650 / 421,290 walks; no flag-0 walk runs
  400 nodes; 198 / 732 flag-1 walks, none with a late pop/jump/return); tower_stacks2.py 4 400 60 → tower_stacks2_4.txt.
* tower_cut_hunt.py 9 8 600 → tower_cut_hunt_9.txt; tower_counter_hunt.py 8 / 10 6 400 → tower_counter_8.txt /
  tower_counter_10.txt; phi_hunt.py 9 8 200 (printed in LOG 12:02): no tower-counter step anywhere (now a theorem).
* periodic_hunt.py all 12 2000 → periodic_all12.txt and rand 21 2000 100000 → periodic_rand21.txt: no periodic
  leftmost walk (the simplest way to make infinitely many jumps).
Labels: everything under MACHINE-CHECKED compiles in EMA.lean; the 'ARGUED' LOG entries (11:02, 11:17, 11:28, 11:48,
11:51, 11:54) are superseded where a MACHINE-CHECKED theorem now exists, and J remains CONJECTURAL / EXPERIMENTALLY
SUPPORTED.  Nothing was committed, pushed or posted by this agent.
