# S Combinator Challenge — results at a glance

**Wolfram's S Combinator Challenge is not solved by this work.** This page summarises what is proved, what is
machine-checked, and exactly what remains open, in both directions. Labels: MACHINE-CHECKED (Lean 4, no `sorry`,
standard axioms only) > PROVED (hand proof) > COMPUTATIONALLY CERTIFIED > EXPERIMENTALLY SUPPORTED > CONJECTURAL.
Details and proofs: `PROOF.md`; results table: `STATUS.md`; how the pieces fit: `PROOF.md`, section "Master Reduction".

## Machine-checked in Lean 4 (`lean/`, re-checked by `code/verify_all.py`)
| result | file | meaning |
|---|---|---|
| **Theorem Q10** (BEKW Question 10) | `Q10.lean` | head reduction of an S-term terminates iff its class in the 35-element model M35 is in F. This answers Question 10 of Barendregt–Endrullis–Klop–Waldmann ("Dance of the starlings") and gives an independent machine-checked proof that head normalisation of S-terms is decidable in linear time |
| Theorem A | `TheoremA_M35.lean` | M35 class outside F ⇒ no head normal form; the model's S-identity is checked by the Lean kernel over all 42,875 class triples |
| **Theorem P2** | `P2_Parity.lean` | the Böhm tree of S·S^j·(SSS)·(SS) is finite iff j is even or j = 1: S-terms can count modulo 2 |
| Proposition Q | `PropQ.lean` | every term whose class in the 39-element productivity model is in F_P is productive (no ⊥ anywhere in its Böhm tree): one half of Conjecture C6, the conjectured answer to BEKW Question 5 |
| Proposition Q″ | `PathModels.lean` | the "infinite" verdicts of the leftmost-path (36 classes) and rightmost-path (19 classes) models are correct |
| Lemma 8, Theorem J | `BarrierJ.lean` | data conservation; a write of closed material onto data happens at most once per Böhm-tree step and wraps all the data at once (the barrier behind "no registers, no tag appends") |
| Lemma P, Theorem LP1 | `LP1.lean` | if S·t·A·B has a head normal form, t's leftmost Böhm-tree path ends at S; hence every term whose M35 class is in F outside the five two-argument-dead classes D2 has a finite leftmost path ending at S |
| Theorems UR-R, UR-C | `URCore.lean` | runs whose head redex stays the only redex are eventually linear counters (type A or II); very likely overlaps Waldmann's "Nimm Zwei" (1997) |
| Obstruction theorems OT, RC, OC, OTD, FH, SL, `canonical_innermost` | `Agent*.lean` | code can only write right combs from a generic datum; such data cannot drive Church-style transfers; from phase 2 on transfers are dirty; single-level data force re-execution after at most two transfer phases |

## Proved by hand (with computer-certified finite facts)
* Theorem O: no bounded-cost two-counter simulation (independently audited).
* Lemmas 8–10, Theorem J, Proposition M: with opaque data, code cannot write into data, rotate it cleanly, or append
  like a tag system in one pass.
* Theorem NM: morphic regularity of head runs is false (square runs), while the weaker R″_PUP holds for every certified run.
* Per-term exactness certificates for every census counter (152/152 at 12 leaves) and for 850/850 random endpoints up to
  640 leaves (loop, nested-loop, call and comb provers); 86/150 sampled parallel (ReplaceAll) runs.
* Master Reduction (PROOF.md): a precise list of what a complete disproof needs, including Lemma W for whole-state
  finite-automaton decoders.

## Open — what would still be needed
**For "S is not universal"** (all three are open research problems):
1. C5′: decidability of MSO properties of Böhm trees. Special cases are open too: the completeness halves of C6
   (= BEKW Question 5, productivity) and C8, and the finite halves of the path models. These are certified up to 16–19
   leaves. A size-change attack on the leftmost half fails for every finite abstraction (FAILED_APPROACHES 29).
2. Configuration-level regularity (R″_PUP) of every head run and of every other evaluation order. The
   non-universality agent's phase programme (agent_work/) is the current attack; its open step is "phase 3 never
   transfers properly" for multi-level data.
3. An argument that Wolfram's "non-universal decoder" falls under the covered classes (the definitional piece).

**For "S is universal":** an explicit emulation. Every design pattern tried so far is blocked by a proved barrier or
failed in bounded searches. The universality agent's current lead is the leftmost-path "descent machine", which has
erasure (agent_work_U/).

## What is not claimed
No proof of universality or non-universality. Several results here turned out to be known (Zachos term, BEKW
Fig. 14 = M35, Padovani's decidability of head normalisation, Waldmann's characterization of one-redex terms); see
the novelty notes in `PROOF.md`. Machine-checked statements are exactly as stated in the Lean files.
