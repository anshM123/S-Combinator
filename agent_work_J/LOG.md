# agent_work_J LOG (Conjecture J agent, 2026-10-27)

Brief (main agent): prove Conjecture J (an infinite leftmost walk makes only finitely many jumps = nodes S p tau with
exactly two arguments), at least for walks from L36-flag-0 terms; with SC.finite_half_of_J (agent_work_EM/lean/EMA.lean)
this would give the leftmost finite half of L36.  If J resists: close as many of the four jump sources as possible and
state exactly what is left.  FINAL due 15:30 EDT.  Labels: PROVED / MACHINE-CHECKED / COMPUTATIONALLY CERTIFIED /
EXPERIMENTALLY SUPPORTED / CONJECTURAL / REFUTED.  All files of this agent live in agent_work_J/.

## 12:31 EDT start (`date`)
* Read agent_work_EM/LOG.md (FINAL, 11:54, 12:10), PROOF.md 'Leftmost-path finite half', EMA.lean definitions
  (C.T, C.step, C.Reach, FH.LChild, FM.tw / Fw / fib_step, SA.rpart, SA2.msl).

## 12:45 EDT — EXPERIMENTALLY SUPPORTED: census of jump SOURCES (jump_anatomy.py)
* Script agent_work_J/jump_anatomy.py classifies every jump node u(j+1) = S p tau by its predecessor u(j): pop, jump,
  computed over a tower stack ('tower'), or computed over a non-tower stack with H(top) = S (tw K) c0 (DP.jump_child:
  K0 delayed discard, K1 discard c0 = S p, K2 S-letter sigma = S.p, K3 c0 = S).  'Separated' = at least one computed
  step since the previous jump.
* all 12 400 -> jump_anatomy_all12.txt (all 58,786 closed terms with 12 leaves, walks <= 400 nodes): sources of the
  separated jumps: tower 3,762, K0 3,492, pop 1,959, K1 1,382, K2 192, K3 92 (no 'other': Lemma Fib).  At most TWO
  separated jumps in any walk (123 walks, all flag 0, all end at the leaf S within 11 nodes); every walk with a
  separated jump is flag 0 and ends; the 5 flag-1 walks run 400 nodes with no separated jump.
* all 10 400: at most 2 separated jumps (1 walk).  rand 31 400 100000 running.

## 12:47 EDT — PROVED (relying on a published theorem): NO leftmost walk ever repeats a node; no eventually periodic
## infinite leftmost walk exists (any flag) — the 'natural first target' for J is closed
* Waldmann's no-spiral theorem (J. Waldmann 2000; reproduced with proof as Theorem 14 in BEKW 'Dance of the starlings',
  literature/BEKW_dance_of_the_starlings.txt, section 'Periodic Terms and Reductions'): there is no S-term M and context C
  (possibly trivial) with M ->+ C[M].  [Proof there: label applications with the right-spine length of the argument;
  the labelled S-rule plus label lifting terminates for bounded labels by RPO; a spiral would give an infinite
  reduction with bounded labels.]  This theorem is NOT machine-checked here; it is used as a cited hypothesis.
* Claim: in a leftmost walk u (FH.LChild (u j) (u (j+1)) for all j), u N = u M with N < M is impossible.
  Proof: each step makes u (j+1) a PROPER subterm of a reduct of u j: a pop u j = S u(j+1) or a jump u j = S u(j+1) x
  (no reduction), or a computed step: args (u j) ->* [u(j+1), d] by head steps, i.e. u j ->+ S u(j+1) d (at least one
  step: a list of length >= 3 must be reduced to reach length 2).  Reduction is compatible with contexts, so
  u N ->* C[u M] with C non-trivial.  If no node u j, N <= j < M, is computed, u M is a proper subterm of u N, so
  u M /= u N by size.  Otherwise u N ->+ C[u M]; u M = u N would be a spiral.  ∎
* Consequences: (i) no eventually periodic infinite leftmost walk (from ANY term; the EM agent's 'natural first
  target' for J); (ii) in an infinite walk all nodes are pairwise distinct, so only finitely many nodes have size
  <= n, for every n (sizes tend to infinity along the walk in the liminf sense); (iii) in a walk with infinitely many
  jumps the jump targets are pairwise distinct and their sizes tend to infinity.
* Plan: machine-check the reduction 'NoSpiral ⇒ no repeated node' in Lean (agent_work_J/lean/JA.lean), with NoSpiral
  stated as an explicit hypothesis (Waldmann's theorem).
