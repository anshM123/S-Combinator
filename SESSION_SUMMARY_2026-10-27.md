# Session summary — 2026-10-27 (main agent plus two subagents)

**The S Combinator Challenge is not solved.** This session turned most of the project's hand-proved core into
machine-checked Lean 4 proofs and published everything to https://github.com/anshM123/S-Combinator. Start with
`RESULTS.md`; the exact Lean statements are in `lean/STATEMENTS.md`; every check is re-run by `python code/verify_all.py`.

## Machine-checked this session (Lean 4.35, no Mathlib, no `sorry`, axioms only propext / Classical.choice / Quot.sound)
* **Finite models and Böhm trees:** Theorem A (M35's S-identity kernel-checked), Theorem P2 (S-terms count mod 2),
  **Theorem Q10** (BEKW Question 10: M35 decides head normalisation) and **BEKW Question 10 as posed** (the automaton of
  BEKW Figure 14 accepts exactly the head-normalising terms; kernel-checked isomorphism), Lemma 4, Proposition Q (soundness
  half of C6 = BEKW Question 5), Proposition Q″ (infinite halves of the path models), Lemma P and Theorem LP1, Theorem C (a
  non-regular Böhm tree: infinitely many distinct subtrees), Lemmas 5 and 6 (Fibonacci peeling, iterator).
* **Evaluation orders and the multiway system:** confluence; Church's theorem for S and Theorem T (a term with a normal
  form terminates in every order and has a finite multiway graph; otherwise no maximal evolution is finite); the head
  normalisation theorem and Proposition CF (Böhm-tree-level control is order-independent); F5 (every reduct has the same
  Böhm tree); Proposition MW (acyclic multiway graph; infinite evolutions have unbounded size; branching cannot mirror
  nondeterministic halting).
* **Barriers for constructions:** Lemmas 8, 9, 10, 11, 12, Corollary 8(ii), Theorem J, the Barrier lemma, Theorem N* with
  its layer bounds (the potential half of Theorem O, also in explicit form), Theorem H with Corollaries H1–H3, Theorem U*,
  the geometry lemmas (access lemma, Lemma G1, Lemma 7 (iii)), Theorems UR-R/UR-C and the UR Observation.
* **The agents' lemmas (re-compiled and recorded by the main agent):** non-universality agent — OT, RC, OC, OTD, FH, FH1,
  FHL, SL, `canonical_innermost`, AB, AB-c, MSL (strict form), YD, the replay lemma, Theorems PA and PB (830 of 836 real
  single-wrapper handlers up to 11 leaves settled, with per-case certified hypotheses); universality agent — W1, W1+, W2,
  W2+ and comb rigidity, `shnf_two_vars` (closed M applied to two variables reaches an S-headed head normal form only for
  M = S or S(S(…(S S)…))).

## The non-universality agents' results (handed back 04:17 and 06:22 EDT)
Chain bound in the generic phase model: a Church chain makes at most 2 proper transfers in every covered case.
Steps 1–2 machine-checked without hypotheses (lean/AgentINNER.lean). Step 3 = Conjecture R3: as first stated (all
ordered data) it is REFUTED by a kernel-computed counterexample with two occurrences of the predecessor
(lean/AgentR3F.lean, `r3_cx_*`), so 'at most 1 transfer from an ordered start' is false; for one occurrence (what the
chain bound needs) it is machine-checked in the covered classes without per-case hypotheses (ALPHA, PBT, CLOSEDGLUE,
PAH, IGEN) and certified with no violation exhaustively up to 13 leaves, but open in general. No chain of length >= 3
among all data up to 11 leaves and 4.5 million random data up to 22 leaves. The replay mechanism (a re-execution
replays the earlier transfer) is machine-checked. D3 remains open.

## Experiments and negative results this session
* E114: a generalised Lemma P with opaque bottoms is a correct sufficient criterion for finite leftmost paths but fails
  to be necessary (5 of 171 resisting terms at 8 leaves); class graphs: the C6 completeness half has one 17-class
  strongly connected component, and node size does not decrease along ⊥_P paths. FAILED_APPROACHES 30.
* E115: BEKW Question 7 (colour change puzzle): no refinement chain with lasting colour alternation among pumping and
  two-site chains (bounds in the entry).

## Still open (unchanged in kind)
C5′ (decidability of Böhm-tree properties; even productivity and leftmost-path finiteness have one half open),
configuration-level regularity (R″_PUP) of all runs in all orders, and the definitional step about Wolfram's
"non-universal decoder". No universal construction either. See `RESULTS.md`, "Open", and `PRIZE_ASSESSMENT.md`.

## Verification
`verify_all.py` passed 97/97 at 04:00 EDT on the working copy, and a fresh clone of the GitHub repository passed
103/103 at 04:15 EDT (`code/verify_all.py` needs only Python 3 with numpy and the Lean 4.35.0 toolchain).
