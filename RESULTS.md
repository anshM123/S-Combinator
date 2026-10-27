# S Combinator Challenge — results at a glance

**Wolfram's S Combinator Challenge is not solved by this work.** This page summarises what is proved, what is
machine-checked, and exactly what remains open, in both directions. Labels: MACHINE-CHECKED (Lean 4, no `sorry`,
standard axioms only) > PROVED (hand proof) > COMPUTATIONALLY CERTIFIED > EXPERIMENTALLY SUPPORTED > CONJECTURAL.
Details and proofs: `PROOF.md`; results table: `STATUS.md`; how the pieces fit: `PROOF.md`, section "Master Reduction";
the exact Lean statements of the headline theorems: `lean/STATEMENTS.md`.

## Headlines
* **Not solved.** Neither universality nor non-universality of S is proved here.
* **BEKW Question 10 is answered and machine-checked, as posed:** the tree automaton in Figure 14 of Barendregt–Endrullis–
  Klop–Waldmann accepts exactly the S-terms with a head normal form (`BEKW_Q10.lean`, on top of `Q10.lean`).
* **Evaluation order does not matter for control or termination (machine-checked for S):** confluence, Church's theorem
  (a term with a normal form terminates in every order), the head normalisation theorem and the invariance of Böhm trees
  hold. Every infinite evolution, in any order, visits terms of unbounded size, so it never settles into finitely many
  forms.
* **Why constructions fail (more than 30 machine-checked barrier theorems):** code cannot write into two live data,
  rotate data cleanly, create 'fuel', hold two data except as a comb, or let a counter grow beside an unread counter
  beyond a fixed potential, and it must read what it uses, at a cost. Every construction route tried so far is blocked
  by one of these or failed in bounded searches; this is evidence, not a proof, that none exists.
* **What a full disproof still needs:** decidability of Böhm-tree properties (open even for productivity, BEKW Question 5,
  and leftmost-path finiteness), regularity of all head runs (R″_PUP), and a definitional argument about Wolfram's
  "non-universal decoder" (see "Open" below).

## Machine-checked in Lean 4 (`lean/`, re-checked by `code/verify_all.py`)

**Head normalisation, Böhm trees and finite models**

| result | file | meaning |
|---|---|---|
| **Theorem Q10** (BEKW Question 10) | `Q10.lean` | head reduction of an S-term terminates iff its class in the 35-element model M35 is in F. This answers Question 10 of Barendregt–Endrullis–Klop–Waldmann ("Dance of the starlings") and gives an independent machine-checked proof that head normalisation of S-terms is decidable in linear time |
| BEKW Question 10, as posed | `BEKW_Q10.lean` | the tree automaton of BEKW's Figure 14 accepts exactly the S-terms with a head normal form (isomorphism with M35 checked by the kernel; the figure's table is transcribed from the paper) |
| Theorem A | `TheoremA_M35.lean` | M35 class outside F ⇒ no head normal form; the model's S-identity is checked by the Lean kernel over all 42,875 class triples |
| Lemma 4, hnf congruence | `Lemma4.lean` | all terms without a head normal form are interchangeable in every context; terms with the same M35 class have a head normal form in exactly the same contexts |
| Proposition Q | `PropQ.lean` | every term whose class in the 39-element productivity model is in F_P is productive (no ⊥ anywhere in its Böhm tree): one half of Conjecture C6, the conjectured answer to BEKW Question 5 |
| Proposition Q″ | `PathModels.lean` | the "infinite" verdicts of the leftmost-path (36 classes) and rightmost-path (19 classes) models are correct |
| Lemmas 5, 6 | `Lemma56.lean` | Fibonacci peeling (S N_j q v reaches S F_(j+1) F_(j+2) in j + 1 steps) and the iterator lemma: the exact runs behind nest and wrapper counters |
| Lemma P, Theorem LP1 | `LP1.lean` | if S·t·A·B has a head normal form, t's leftmost Böhm-tree path ends at S; hence every term whose M35 class is in F outside the five two-argument-dead classes D2 has a finite leftmost path ending at S |
| Theorem C | `TheoremC.lean` | the Böhm tree of the 18-leaf term K·W_1 has infinitely many distinct finite subtrees (sizes 11 + 2r for every r >= 1): Böhm trees of S-terms are not regular in general, so a decision method for their MSO properties (C5′) must go beyond regular trees |
| **Theorem P2** | `P2_Parity.lean` | the Böhm tree of S·S^j·(SSS)·(SS) is finite iff j is even or j = 1: S-terms can count modulo 2 |

**Evaluation orders and the multiway system (classical facts, machine-checked here for S)**

| result | file | meaning |
|---|---|---|
| Confluence, Proposition MW(e) | `Confluence.lean` | S-reduction is confluent (normal forms are unique); a decoder that respects reachability cannot read two different halting outcomes of a nondeterministic machine from S's multiway system (true of every confluent system, SK included) |
| Proposition CF, head normalisation theorem | `CF.lean`, `Standard.lean` | if any evaluation reaches a head normal form, head reduction does too; and whichever evaluation order reaches a head normal form, it finds the same head and the same number of arguments, with joinable arguments: control flow at Böhm-tree level does not depend on the evaluation order |
| F5: Böhm trees are invariant under reduction | `BTInv.lean` | a term and every reduct (any evaluation order, any redex choices) have the same Böhm tree to every depth, so every Böhm-tree property is order-independent |
| **Theorem T** (except decidability) | `TheoremT.lean` | termination is all-or-nothing: a term with a normal form has no infinite evolution in any order (Church's theorem for S) and a finite multiway graph; a term without one has no finite maximal evolution. With Waldmann's theorem (cited) this rules out 'the evolution stops' as a halting signal |
| Proposition MW(a),(b) | `MW.lean` | in every evolution order the multiway graph of an S-term is acyclic, and every infinite evolution visits terms of unbounded size, so it never settles into finitely many forms |

**Barriers for constructions**

| result | file | meaning |
|---|---|---|
| Barrier lemma | `Barrier.lean` | every S-term P run on two opaque arguments [P, x, y | r] hands control to an argument before it touches anything below them: loop bodies can never touch their accumulator |
| Lemmas 8, 9 (core), Corollary 8(ii), Theorem J | `BarrierJ.lean` | data conservation; no write into data while two data are live; data stay in control; a write of closed material onto data happens at most once per Böhm-tree step and wraps all the data at once (the barrier behind "no registers, no tag appends") |
| Lemma 10 | `Lemma10.lean` | no junk-free rotation: with two data, the bottom one can be brought in front of the other only together with a second copy of itself |
| Lemmas 11, 12 | `ReadCost.lean` | full-read principle (a normalising run reads at least one of any three marked arguments) and right-depth cost (reading at right-depth D costs at least D steps) |
| Theorem N* (list form), Corollary N* (layer bound) | `NStar.lean` | potential bound for counters: along a Böhm-tree path that never reads the cores, the layers that can still be added above one counter are bounded by a potential that never increases; explicitly, a counter with d layers of hole depth h under a context of hole depth H reaches at most d + H/h layers (unread core x, so its potential is 0) — the core of Theorem O (no bounded-cost two-counter simulation) |
| Theorem H, Corollaries H1–H3 | `TheoremH.lean` | code that never inspects its inputs behaves the same on every input class of M35: no pair of gadgets S g1 g2 can hold two data cleanly, only the six nest classes can hold two data, and no S-term can hold three |
| Theorem U* | `TheoremUstar.lean` | a head run that starts without 'fuel' (no closed element directly below data) never creates any, even through zero tests that execute marked data: counter-transfer designs need fuel built into the program |
| Theorems UR-R, UR-C, the Observation | `URCore.lean`, `URObs.lean` | runs whose head redex stays the only redex are eventually linear counters (type A or II); the Observation shows this is exactly 'one redex at every step', so it holds in every evaluation order; very likely overlaps Waldmann's "Nimm Zwei" (1997) |

**The two agents' programmes**

| result | file | meaning |
|---|---|---|
| `shnf_two_vars`, comb rigidity for any two data | `AgentWR.lean` | for closed M, M x y reaches an S-headed head normal form only if M = S or M = S(S(…(S S)…)): with two opaque arguments, S-code either hands control to an argument or is a comb |
| Lemmas W1+, W2, W2+ and comb rigidity | `AgentW1F/W2/W2R.lean` | leftmost-path (descent-machine) rounds: a single datum only forms Fibonacci words; with two data no code can store them, and the only code that carries both across a round is a comb S(S(…(S S)…)), which just swaps them Fibonacci-style — no second independent store |
| Theorems PA, PB; Lemmas FH1, FHL | `AgentPA/FH1/FHL.lean` | for single-wrapper phase-2 handlers (glued in pattern alpha, or beta with c0 = S·a1), the next phase never makes a proper transfer, given replay guards certified per case: 830 of 836 real cases up to 11 leaves settled |
| Lemmas AB, AB-c, MSL (strict form), YD, replay lemma; Lemma W1 | `AgentAB/ABC/MSL/MSLS/YD/REPLAY/W1.lean` | steps of the two agents' programmes: no P-onto-Y glue once the P-region is large; every glued P-wrapper of a multi-level datum is good; an early glued-down y kills proper transfers; a single-wrapper phase-2 transfer replays as a phase-3 re-execution; a descent-machine round adds at most one closed wrap to a single-copy datum |
| Obstruction theorems OT, RC, OC, OTD, FH, SL, `canonical_innermost` | `Agent*.lean` | code can only write right combs from a generic datum; such data cannot drive Church-style transfers; from phase 2 on transfers are dirty; single-level data force re-execution after at most two transfer phases |

## Proved by hand (with computer-certified finite facts)
* Theorem O: no bounded-cost two-counter simulation (independently audited). Its ingredients — Theorem N*, Lemma 8,
  Theorem J, Lemmas 11 and 12 — are machine-checked above; the residual-walk argument that combines them is not.
* Proposition M: with opaque data, code cannot append like a tag system in one uniform pass (the barrier lemmas it
  rests on — Lemmas 8, 9, 10, Theorem J and the Barrier lemma — are machine-checked above).
* Theorem NM: morphic regularity of head runs is false (square runs), while the weaker R″_PUP holds for every certified run.
* Per-term exactness certificates for every census counter (152/152 at 12 leaves) and for 850/850 random endpoints up to
  640 leaves (loop, nested-loop, call and comb provers); 86/150 sampled parallel (ReplaceAll) runs.
* Master Reduction (PROOF.md): a precise list of what a complete disproof needs, including Lemma W for whole-state
  finite-automaton decoders.

## How the pieces fit (PROOF.md, Master Reduction)
A universal emulation needs an encoder, an evaluation order and a halting detector that is not itself universal.
* Halting = "the evolution stops": impossible in every order (Theorem T, machine-checked except the decidability of
  normalisation, which is Waldmann's theorem, cited).
* Halting = a property of the Böhm tree: control at Böhm-tree level is the same in every evaluation order
  (Proposition CF and F5, machine-checked). Such detectors are excluded once the property is decidable.
  Head normalisation is (Theorem Q10, machine-checked); productivity and path finiteness are decided by finite models
  in one direction (machine-checked), and the other direction is open.
* Halting = a finite-automaton test of the current state: excluded under configuration-level regularity of the runs
  (R″_PUP; Lemma W). This is open in general. It is proved per term for every certified run. The barrier lemmas
  above (machine-checked) explain why constructions fail: code cannot write into live data, rotate data cleanly,
  read without paying, or grow one counter beside an unread one.
* Anything else: outside every result here (the definitional step).

## Open — what would still be needed
**For "S is not universal"** (all three are open research problems):
1. C5′: decidability of MSO properties of Böhm trees. Special cases are open too: the completeness halves of C6
   (= BEKW Question 5, productivity) and C8, and the finite halves of the path models. These are certified up to 16–19
   leaves. A size-change attack on the leftmost half fails for every finite abstraction (FAILED_APPROACHES 29), and
   neither class-level acyclicity nor node size proves the C6 or leftmost halves (E114, FAILED_APPROACHES 30).
2. Configuration-level regularity (R″_PUP) of every head run and of every other evaluation order. The
   non-universality agent's phase programme (agent_work/) is the current attack; its open steps are "phase 3 never
   transfers properly" for the remaining cases (6 single-wrapper cases up to 11 leaves and the multi-wrapper class)
   and "re-execution is call-like".
3. An argument that Wolfram's "non-universal decoder" falls under the covered classes (the definitional piece).

**For "S is universal":** an explicit emulation. Every design pattern tried so far is blocked by a proved barrier or
failed in bounded searches. The universality agent's current lead is the leftmost-path "descent machine", which has
erasure (agent_work_U/).

## What is not claimed
No proof of universality or non-universality. Several results here turned out to be known (Zachos term, BEKW
Fig. 14 = M35, Padovani's decidability of head normalisation, Waldmann's characterization of one-redex terms); see
the novelty notes in `PROOF.md`. Confluence, Church's theorem, the head normalisation theorem and the invariance of
Böhm trees are classical; they are machine-checked here for S so that the order-independence steps are rigorous.
Machine-checked statements are exactly as stated in the Lean files.
