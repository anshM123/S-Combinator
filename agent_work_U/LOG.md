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
