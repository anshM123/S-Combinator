# Session summary — 2026-10-26 (overnight autonomous run)

**Bottom line: the S Combinator Challenge is NOT solved, in either direction. Nothing has been submitted or published.**

**Latest of all (2026-10-26, evening — UR-C in Lean, a correction, Theorem DK):**
* **Theorem UR-C machine-checked** (lean/URCore.lean, `ur_classification` / `ur_counter`; 19 theorems, 0 errors, no
  sorry; standard axioms). Every run whose head redex stays its only redex for ever is eventually a type A or type II
  linear counter. The Observation (head redex the only one ⇔ `urForever`) is still a hand proof.
* **CORRECTION:** one-redex evolutions can descend into arguments for ever: from [S, S p q, c] the redex moves into the
  argument and the outside freezes. The enumerations had stopped at such steps. So "every unique-redex S-term is a
  linear counter" (below) and R57's "none with ≤ 9 leaves" are REFUTED as stated. Both hold for head-unique runs; with
  descents the minimum is 9 leaves (S(S(SS))(S(SS))(SS), checked independently on plain trees).
* **Theorem DK (PROVED):** a descending linear counter with base K = S(SS)(SS), Y_{n+1} = S S Y_n:
  [SS, SS, Y_n] → [SS, SS, Y_{n+1}] in n + 2 steps. All 140 forever-descending one-redex terms up to 14 leaves enter it
  by step 5. Open: the descending class at every size. **Not new:** K·K is the Zachos term STT(STT) (BEKW §2, our E20),
  and Waldmann's "Nimm Zwei" (1997) characterizes all one-redex-forever terms; no novelty is claimed.
* A background subagent (started at the user's request) works on the constructive direction under agent_work/.

**Latest (2026-10-26, night — parallel evaluation):**
* **Lemma LZ (PROVED):** P(S a_1 a_2 a_3 a_4 ⋯) = a_1 a_3 (a_2 a_3) P(a_4) ⋯ and P(S a_1 a_2) = S P(a_1) P(a_2) give an exact
  *lazy* parallel machine: elements carry pending passes and are evolved only when opened. Direct ReplaceAll passes hit a
  1.5M-node cap after 66–130 passes, and the lazy machine runs 20,000 passes per term in under a second. It is checked
  against the direct passes wherever those fit.
* **Theorem PL (PROVED):** S(S(S(S(SSS)(SSS))))SS under parallel evaluation is one growing loop over right combs of
  L = S(S(SS)) — simpler than its nested head run. It is the first exact parallel run that differs from its head run.
* **Theorem LP-par (PROVED per term):** the loop prover with the parallel engine, extended to comb families that keep
  evolving, certifies 86 of the 150 census-sample parallel runs, and all 86 are checked against 400,000 concrete
  passes. Most of the remaining 64 time out.
* **Unique-redex terms classified up to 17 leaves (Theorems UR-Φ, UR-Φ-II, PROVED + computer-certified):** all 2,087 terms with a unique redex for 3,000 steps keep it for ever and are linear counters, identical in every evaluation order.
* **Round machine for unique-redex runs (Lemmas R, R′, PROVED):** every infinite head run has infinitely many opcode-0 steps (between them it descends one left spine), and a unique-redex round [c, S c, d] is a two-register machine on c's left spine; it matches the concrete runs in all 268,650 rounds checked. Bases enumerated to 13 leaves: 89, with 13 return patterns. The steady states up to 17 leaves use two of them.
* **Theorem UR-R (PROVED, every size):** every unique-redex run enters the Φ-regime within three rounds; Φ-elements always end in the gadget B = S(SSS)S; the run is then a deterministic map on one element. Its orbits are linear counters of type A or II (Theorem UR-C, PROVED: every transition rule machine-checked on all real runs and ≈ 1.76M sampled transitions). So every head-unique S-term, at every size, is a linear counter in every evaluation order. [CORRECTED: this first said "every unique-redex S-term"; descending one-redex evolutions are a separate class, see Theorem DK above.]
* **Adversarial search (E106):** maximising the opcode words' Lempel–Ziv complexity over ≈ 1,300 terms finds nothing irregular — the 30 most complex runs are all certified loop runs. Thin runs beyond the unique-redex class (118 at 13–15 leaves) are all certified loops too (E105). Data correction E104: 2,087 unique-redex terms ≤ 17 leaves.
* **Lean 4 (E107):** Theorem UR-R's core — every unique-redex-forever list reaches Φ-states and stays in them — is machine-checked (lean/URCore.lean, 11 theorems, standard axioms only, no sorry).
* Randomised differential tests confirm the lazy parallel machine and the canonical aging rule on 1,100 random terms (31,639 passes) and 1,100 random aging cases.
* verify_all: 60 checks (LZ ×2, PL, LP-par ×4, unique-redex ×7, round machine, UR-R, UR-C ×3, E106, Lean, fuzz added).

**Latest (2026-10-26, last part of the run):**
* **Morphic R″ refuted (Theorem NM, PROVED).** Lemma S: in a morphic word, a marker whose two-occurrence factors are all
  rare occurs only O(√N) times among the first N letters (elementary proof, any growth). The nested-loop certificates give
  the exact opcode words of the two square runs for all n (code/nest_words.py), in which such a marker occurs Θ(N^{2/3})
  times — so their window words are not morphic. The structural conjecture for leftmost-outermost runs is now R″_PUP only
  (what Proposition UB needs; every proved run satisfies it).
* **Order-independent infinite evolution (Theorem UR, PROVED).** t_0 = S(SSS)S(S(SSS)S) (10 leaves) has exactly one redex
  at every step forever, so its multiway graph is a single path and every evaluation order gives the same evolution (a
  linear counter). None with ≤ 9 leaves; 2, 3, 10, 26 such terms (for 3,000–5,000 steps) with 10–13 leaves, all of the same
  linear-counter kind.
* **Leftmost-innermost (call-by-value) evolution:** it either descends for ever into non-normalising arguments (the rest
  of the term freezes; bounded-prefix detectors are then decidable) or contracts at a fixed depth for ever (t_0 does).
  All non-normalising terms ≤ 8 leaves descend.
* **Call prover hardened:** RESUME is used only when its barrier holds, and otherwise simply withdrawn; counters 147/152
  and census sample 150/150 unchanged; the template-driver fallback proves the last binary counter of the 40–80-leaf
  hunt, a scheme-inference fix proves the base-3 call run of the 25–40-leaf hunt (now 150/150), and fixing an
  opcode-encoding bug (opcodes ≥ 10 misaligned cycle starts; completeness only) proves the last 40–80-leaf run
  (now 100/100), and new hunts at 80–160 and 160–320 leaves are 100/100 (E85, E86), and at 320–640 leaves 100/100 (E87; a third non-morphic square run) — 850 of 850 hunt endpoints — every run of every
  hunt is proved; Theorems CD, CD2, CD3 and NS prove the last five census counters exactly — all 152 counters of the 12-leaf census are
  proved exact (E88–E93); audits of the comb and loop
  provers each found one small gap (first comb cycle; residue-pass anchor), both fixed with no certificate lost;
  verify_all now has 33 checks (Theorem NM and Theorem UR added), 33/33 PASS.

**Rules correction (re-read 2026-10-26, later):** the prize home page (combinatorprize.org) requires a submission 'in the
form of a technical research paper, suitable for publication', with a full proof; it must be the original work of the
submitter(s), name all relevant contributors, and cannot be anonymous. An earlier note here said no paper was required —
that was wrong. Whether and how AI-assisted work may be submitted is a question for the user (and the committee).
Everything below is recorded in detail in PROOF.md, STATUS.md (rows R32–R50), EXPERIMENTS.md (E55–E68),
FAILED_APPROACHES.md (items 30–32) and NEXT_STEPS.md. Labels as everywhere: PROVED / COMPUTATIONALLY CERTIFIED /
EXPERIMENTALLY SUPPORTED / CONJECTURAL.

**Window caveat and its resolution (2026-10-26, later):** Proposition UB's bounded-time-detector case needs the morphic
structure of the first k list elements for every k (R″_{k,d}); UB was corrected to say so. The certificates first gave
only k = 3; whole-list certificates (Corollaries LP′ and CA′: loop pushes as graded segments, call residues as a recursive
list grammar) now give every k for every proved run — 150/150 census sample, 100/100 larger sample, every proved
counter (E69, E70, E71). Still per term: R″ for all terms is open.

**Conjecture update (later):** the bridge to the prize criterion (Proposition UB) needs only window words that are
*effectively profinitely ultimately periodic* (Carton–Thomas decide MSO for those; morphic words are a special case).
Hunts at 17–24 and 25–40 leaves proved 200/200 and 147/150 endpoints; two of the rest are *square* nested loops
(round m = m identical blocks of length ≈ 12m), probably not morphic but profinitely ultimately periodic (Lemma PUP).
So the morphic form of Conjecture R″ is in doubt; the form UB needs survives everything seen. A nested-loop prover
(Theorem NL) now proves the square runs; a hunt at 40–80 leaves proved 98/100 (median endpoint 55 leaves). Parallel
evaluation does not inherit these certificates: in 301 of 302 runs, elements without normal form wait below the first
three and evolve forever under parallel evaluation (E75, E76).

**Soundness audit (later):** the nested-loop prover first used one opaque atom and one loop variable for every
nesting level, so an inner loop's stored pushes could be mislabelled (they really do depend on the outer loop's
variable). The square-run proofs were withdrawn, the prover fixed (separate atoms and variables per level), and all
three square runs re-proved with the corrected code (E77). The other provers were checked for the same flaw and do not
have it.

## Re-verify everything in one command
From `code/`: `python verify_all.py` — 33 checks (symbolic derivations and concrete certificates); **33/33 PASS** (last full run, end of the overnight session, about four minutes).

## New results
| Result | Status |
|---|---|
| **Theorem BC** — the head run of SSS(SS)S(SS(SS)) is an exact infinite binary counter: checkpoints at 144·2^k − 48k − 104, no normal form, morphic opcode word | PROVED; matches 589,144 steps exactly |
| **Theorem TC** — a 23-leaf term's head run is an exact ternary counter | PROVED; matches 1,407,063 steps |
| **Theorems K, K′** — for every base μ ≥ 2 an explicit S-term's head run counts exactly in base μ (2μ + 17 leaves for μ ≥ 3); the base is a numeral-like gadget inside a fixed driver | PROVED for all μ (gadget treated as an opaque symbol); certified μ = 3..8 |
| **Theorem CA (call algebra)** — composable subroutine calls in pure S | PROVED |
| **Theorem N (S-numerals)** — (SS·)^{n−1}SS iterates calls: loops / case analysis | PROVED |
| **Theorem T** — for every evolution order, termination is all-or-nothing and decidable | PROVED (from standard theorems) |
| **Proposition UB** — if every head run is effectively morphic (Conjecture R″), no leftmost-outermost emulation with a bounded-window detector is universal | PROVED conditionally |
| **Barrier lemma** — no S-term touches the list below its two arguments before passing control; hence calls carry no data and numeral loops cannot iterate a transformation of their accumulator | PROVED |
| **Lemma PH** — a parallel (ReplaceAll) pass = one head step + one pass inside every waiting element | PROVED |
| **Transfer lemma + Theorem CA-par** — head-run behaviour carries over to parallel evaluation when every relevant slot (opened, or a part of a relevant product) waits in normal form; hence every tree call keeps its exact time under parallel evaluation (normal-form arguments). The first version of the lemma had a gap (relevance closed only under the head part) — found by testing and corrected | PROVED (corrected); checked on 146 + 13 calls |
| **Theorem BC2** — the robust counter S(SS)S(S(S(SSS)))S is an exact binary counter of a second kind (levels with three copies, return form R′); events at 32·2^k − 5k − 10, morphic opcode word | PROVED; certified on 10^6 steps |
| **Parallel-robust counters** — the Theorem BC2 counter runs identically under both orders for ≥ 200,000 steps (argued for all steps); the Theorem BC counter does not | PROVED for 200,000 steps |
| **Time-to-data channel** — under parallel evaluation a waiting 'clock' term encodes elapsed time (frozen under leftmost-outermost) | COMPUTATIONALLY CERTIFIED |
| **Proposition CF** — control flow (which argument receives control) is the same under every head-fair evaluation order; clocks/timeouts change syntax and timing only, never control | PROVED (Church–Rosser + standardization) |
| **Automatic exact-structure prover** — proves 144 of the 152 counter-type head runs of the 12-leaf census exact (all 111 binary counters) and all 150 of a random sample of the other endpoints (call prover 62, comb prover 22, loop prover 66) — an estimated ≥ 98% of all 18,326 runs; 147/152 counters; and 100/100 endpoints of random 13–16-leaf terms, each cross-checked; R″_{3,d} (first three list elements) holds for them | PROVED (per-term soundness checks) |
| **Theorem LP (loop runs)** — loop lemma LB + cycle lemma LC with comb tokens λ^{n+b}·X: multi-loop cycles, combs anywhere in the list, loop variables in several places, context combs F^m(X) (linked lists); per certified term the run is forever u_0 B_1^{n+b_1} u_1 ⋯ (morphic) | PROVED (lemmas); per-term certificates with instance cross-checks |
| **Proposition MW (multiway topology)** — (size, −leaf depth) increases strictly at every step: no S-term reduces to itself, multiway graphs are DAGs, sizes diverge, reachability is decidable; reduction-closed multiway detectors equal one Gross–Knuth evolution; S's branching cannot mirror nondeterministic branching (nor can SK's) | PROVED (cofinality of Gross–Knuth reduction cited) |
| Census to 12 leaves (18,326 endpoints) and random samples to 40 leaves: every head run is bounded, a single counter, a nested counter or a base-2/3 counter | EXPERIMENTALLY SUPPORTED (evidence for R″) |

## Corrections made during the session
* "All binary counters are one machine" — withdrawn: only 21 of 111 census binary counters are the Theorem BC machine.
* The ternary term has 23 leaves (not 22). The call-time closed form is 2^{j+4} − 8 (not 2^{j+3} − 8).
* Base-4/5/6 radix hits were detector artifacts (only bases 2 and 3 occur in real runs).
* "No short linear recurrence under parallel evaluation" is generic for all small S-terms, so it is not evidence of
  complexity.
* The first no-accumulation sketch missed that transformed copies can exist; the barrier lemma gives the correct proof.
* The first transfer lemma closed relevance only under the head part b of a product; opening b·c also exposes c. Found
  when the binary counter's parallel run diverged at step 20 despite passing the old test; corrected.

## What the prize actually requires (re-checked against Wolfram's announcement)
* Universality = emulation via an encoder, detector and decoder that are not themselves universal. Two definitions are
  left open: strong (the multiway system) and weak (some evolution order). The announcement prefers Wolfram Language
  code or accepts an abstract proof, but the prize home page requires a technical research paper suitable for
  publication (see the rules correction at the top).
* So a universality proof may choose one order; a disproof must cover every order and every admissible decoder.

## Where it stands
* **Leftmost-outermost:** every mechanism found is a fixed recursion; calls carry no data; loops cannot accumulate. The
  leftmost-outermost part of a disproof is exactly effective Conjecture R″ (open). The only remaining leftmost-outermost
  route to data-dependent control is executing data.
* **Parallel evaluation:** the leftmost-outermost limits do not transfer (time becomes data through waiting clocks).
  Clocks found so far are structured (linear factor complexity, slowly drifting rates) but not exactly predictable;
  a perfect unary clock (list growing by exactly one per step forever) is impossible (the front would descend forever
  into first arguments).
  The parallel run of the binary-counter term looks quasi-regular for 160 passes. This is the best lead for a
  universality construction, and the part a disproof cannot ignore. No construction exists.
* Honest estimate: neither a universality construction nor a complete disproof is in reach of this project's sessions;
  nothing here should be submitted.

## Map of the remaining gap (see PRIZE_ASSESSMENT.md, top)
1. Halting = evolution stops: impossible for every order (Theorem T).
2. Halting = a control-flow / Böhm-tree event: order-independent (Proposition CF); reduces to the finite S-model
   conjectures (supported, unproved).
3. Bounded-window syntax under leftmost-outermost: reduces to effective R″_PUP (Proposition UB with Carton–Thomas;
   proved for every certified run, open in general; the morphic form of R″ is false — Theorem NM).
4. Syntax under other orders: the only place the order matters (syntax/timing only); open. New: unique-redex terms
   (Theorem UR) make the order irrelevant; leftmost-innermost either freezes the term from outside in (decidable for
   bounded-prefix detectors) or contracts at a fixed depth.
