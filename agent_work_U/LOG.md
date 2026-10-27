# agent_work_U LOG (UNIVERSALITY agent, 2026-10-27)

Brief: construct a universal emulation by S alone (any evaluation order or multiway), with a non-universal
encoder/detector/decoder.  Labels: PROVED / MACHINE-CHECKED / COMPUTATIONALLY CERTIFIED / EXPERIMENTALLY SUPPORTED /
CONJECTURAL / REFUTED.  Deadlines (coordinator): INTERIM summary 04:00 EDT, refresh ~every 2 h, FINAL summary by 15:30 EDT.
All files of this agent live in agent_work_U/.

## 01:15 EDT start
* Read: PROOF.md (prize target, Theorem SI, U/U*, pump, write-pass, OT/OTD/SL, full re-execution frontier, bridge UB),
  agent_work/LOG.md, NEXT_STEPS.md head.  Tools: code/hc.py, code/symb.py, agent_work/hm.py.

## 01:40 EDT  Direction chosen: the DESCENT MACHINE (leftmost-outermost along the leftmost Böhm path)
* Observation (PROVED, elementary): leftmost-outermost evaluation restricted to the leftmost Böhm path is the
  deterministic list machine DM:  |L| >= 3: [a,b,c|R] -> ch(a)++[c, b.c|R];  |L| = 2: [c,d] -> ch(c);  |L| = 1: [c] -> ch(c);
  |L| = 0: the path ends at the leaf S.  (Leftmost-outermost reduces inside c of the hnf S c d before anything in d, so d
  is frozen as long as c's evaluation does not finish.)  So the DM HAS ERASURE at round ends ([c,d] -> ch(c)), unlike the
  bare head machine: e.g. state SS.y.z => z ("KI"), S(SS).y.z => y.z (clean application), SSSS.z => z (identity),
  (S.x1).y => x1 (unboxing drops y).  By Lemma P (PROOF.md) the DM run of t is embedded in the head run of t A B (the
  erased parts become trailing arguments that are never touched), so a universal DM program would also give a universal
  head run (junk buried at the bottom).  Plan: catalogue DM macro-transitions of code applied to opaque data, then try to
  build a 2-stack / counter / tag machine from them.
* EXPERIMENTALLY SUPPORTED / PROVED-by-inspection (agent_work_U/dm.py, catalog.py, lincat.py, headcat.py): DM
  macro-transitions of closed code on opaque data.  2 args: S x y => x (K), SS x y => y (KI), S(SS) x y => x y,
  S(S(SS)) x y => y(x y), SSS x y => x(S x)y, ... (126 shapes <= 7 leaves).  3 args: NO linear transition <= 8 leaves;
  the deepest argument x3 is never the head and is always passed through unchanged as the LAST argument (97 shapes
  <= 8 leaves, all of form x1(...)...x3 or x2(...)...x3).  Order principle behind it (elementary): an element only
  absorbs the element directly below it; a lower element reaches a higher one only as a rising copy, so a receiver
  below a datum gets it only as x2(x1 x2) ('self-bundled').  Consequence: Scott/Church case analysis 'k x s' with the
  continuation k BELOW the fields x, s is impossible in one round; erasure needs the whole list to collapse.
* COMPUTATIONALLY CERTIFIED (bounded, negative): combhalve.py 5 16 3000 — no closed q, v <= 5 leaves for which the DM
  run of [N_j, q, v] (N_j = j nested S over S) returns to some [N_k, q, v] with a non-constant shift k - j (j <= 16).
  wordround.py 4 2 5 4 4 400 — no (P, A <= 2 leaves, B <= 5, E <= 4) for which the DM maps every word state
  [P, w, E] (w in {A,B}^{<=4}) back to some [P, w', E]: 'fixed-prefix word rounds' do not exist in this range.
* Analysis (PROVED, elementary): with data D1 above D2 in the list, every element directly above D2 contains D1 until
  D2 is absorbed or executed; hence closed code can never write e.D2 while D1 is live (the DM analogue of Lemma 9/RC),
  the deepest datum can only be passed through, absorbed, or made the receiver of a self-bundle D2(X.D2).  Data can be
  modified only when topmost; bringing a lower datum to the top costs a bundle (A,B) -> (B, A.B) (Fibonacci swap).
* Literature facts used (BEKW 'Dance of the starlings', literature/): Waldmann's top-termination (no reduction has
  infinitely many root steps; every S-term is infinitary normalising), the QQQ non-termination criterion, and
  'S-terms have order 3' (an S-term applied to variables hands control to x1 or x2 only; no M with M x y ->> M(x y)).
  With PROOF.md's Proposition CF (control flow is order-independent) this means: every infinite evolution converges to
  a unique limit tree, and universality must come either from Boehm-tree-level control (which would refute the
  HORS conjecture C5/C5') or from syntax inside hnf-free head runs.
