# Prize assessment — Wolfram S Combinator Challenge ($20,000)

_2026-10-25. Status labels as in PROOF.md. Nothing here has been released or submitted._

## Update 2026-10-27, early morning (machine-checked core; three workers) — read first
**Still not solved; nothing submitted.** The repository is public on GitHub (anshM123/S-Combinator) at the user's
request; the prize submission itself still needs the user's approval. The one-page summary is `RESULTS.md`.
* **Machine-checked in Lean 4 (no `sorry`, standard axioms; all in `code/verify_all.py`):**
  * Finite models: Theorem Q10 (BEKW Question 10: M35 decides head normalisation), Theorem A, Lemma 4, Theorem P2
    (Böhm-tree finiteness counts mod 2), Theorem C (a non-regular Böhm tree), Proposition Q (soundness half of C6 = BEKW
    Question 5), Proposition Q″ (the 'infinite' halves of the path models), Lemma P and Theorem LP1.
  * Evaluation orders: confluence, Church's theorem for S and Theorem T (termination is all-or-nothing, finite multiway
    graphs; only the decidability is cited, Waldmann 2000), the head normalisation theorem and Proposition CF (control
    flow is order-independent), F5 (Böhm trees invariant under reduction), Proposition MW(a), (b), (e).
  * Barriers: Lemmas 8, 9, 10, 11, 12, Corollary 8(ii), Theorem J, Barrier lemma, Theorem N* with its layer bound,
    Theorem H with Corollaries H1–H3, Theorems UR-R/UR-C.
  * The agents' lemmas: OT, RC, OC, OTD, FH, SL, AB, AB-c, MSL, YD, replay lemma; W1, W1+, W2, W2+ (comb rigidity).
* **What MW(b) settles about the rules.** Every infinite evolution, in every order, visits terms of unbounded size, so
  "only a finite number of distinct forms" is false for every infinite evolution. A disproof therefore has to take the
  "essentially finite" or "jump-ahead" route: exact symbolic descriptions (R″_PUP) of all runs.
* **Still open, both directions.** Disproof: C5′ (MSO properties of Böhm trees; even the completeness half of C6 and the
  finite halves of the path models are open, and E114 shows they have no class-level or simple size proof), R″_PUP for all
  runs and orders, and the definitional step. Proof: no construction; every design tried meets a machine-checked barrier.
* **Non-universality agents (04:17 and 06:22 EDT):** in the generic phase model a Church chain of proper transfers has at
  most 2 transfers in every covered case (no longer chain among all data up to 11 leaves or 4.5 million random data up
  to 22 leaves). Steps 1–2 are machine-checked outright; step 3 (Conjecture R3) is machine-checked for the covered
  classes. R3 as first stated (all ordered data) is REFUTED by a kernel-computed counterexample with two occurrences of
  the predecessor, so 'at most 1 transfer from an ordered start' is false; the chain bound needs R3 only for one
  occurrence, which is open but certified exhaustively up to 13 leaves. A universal mechanism would therefore have to re-execute frozen
  values or iterate data-blind calls. Open: R3 in general, D3 ('re-execution is call-like'), the phase decomposition of
  all head runs. (PROOF.md, 'Chain bound in the generic phase model'.)
* **Parallel-evaluation agent (11:28 EDT):** no universal construction under ReplaceAll. Machine-checked: every
  evaluation order is the head run re-timed (Theorems PT, PT-all), so the head-run barriers transfer to every order
  and the choice of order changes only timing and syntax inside elements. The remaining universality lead is precise:
  Theorem RR — timing races with prescribed polynomial durations would give universality under ReplaceAll with a
  linear-time detector; no such races are known.
* **Final agent results (10:12 EDT):** (1) R3 is machine-checked without conditions for every single-wrapper handler
  of ordered data with one occurrence of the predecessor, so the two-transfer chain bound holds for every chain whose
  second transfer is single-wrapper or FH (all observed chains); multi-wrapper R3 is open. (2) The leftmost-path finite
  half (and the rightmost one) is reduced in Lean to one conjecture, EM: every infinite leftmost walk is eventually
  monotone (finitely many pops, jumps and returns). Proving EM would make leftmost-path finiteness decidable via the
  36-class model (the other half is Proposition Q″), settling detector class (D2′) for that path.
* **Work in progress (3 workers until 16:30 EDT):** the non-universality agent's phase programme (open step: phase 3 of
  multi-level data cannot transfer properly), the universality agent's descent machine (open: harmless stale bundles),
  and the main agent's verification and formalisation.

## Update 2026-10-26, evening (UR-C in Lean; a scope correction) — read first
**Still not solved; nothing submitted or published.**
* **Theorem UR-C is machine-checked** in Lean 4 (lean/URCore.lean: `ur_classification`, `ur_counter`; no sorry,
  standard axioms). Together with UR-R: every run whose *head* redex stays its only redex for ever is eventually a
  linear counter of type A or II.
* **Correction:** the update below overstated the class. A one-redex evolution can also *descend*. From the active list
  [S, S p q, c] the only redex moves into an argument and the outside freezes, and this can recur for ever: the smallest
  example is S(S(SS))(S(SS))(SS), 9 leaves. Those evolutions are not covered by UR-R/UR-C.
* **Theorem DK (PROVED)** covers every forever-descending one-redex term found: all 140 up to 14 leaves enter one
  descending linear counter (base K = S(SS)(SS)). **Not new:** K·K is the Zachos term STT(STT) (BEKW §2, our E20). Waldmann's
  "Nimm Zwei" (1997) characterizes all one-redex-forever terms, so UR-R/UR-C/DK very likely overlap with known work.
* The one-redex class is therefore settled up to 14 leaves. At every size it is settled for head-unique runs only, and
  the descending part at every size is open.
* None of this touches the open core: terms with several redexes.
* The construction subagent (started at the user's request) found NO universality construction. It proved, and
  machine-checked in Lean, further obstructions: Theorem OT (data written by code cannot drive transfers), Lemma RC
  and Lemma OC. The constructive loophole is now narrower: dirty wrappers, duplicated data or full re-execution.

## Update 2026-10-26, night (unique-redex class settled) — CORRECTED (see the update above)
**Still not solved; nothing submitted or published.** Gap (4), order independence: one whole class is now settled at
every size (PROOF.md, Theorems UR-R and UR-C, hand proofs with every lemma machine-checked on all real runs and about
1.76 million sampled transitions): **every S-term that has exactly one redex at every step for ever is, after finitely
many steps, a linear counter of type A or II, in every evaluation order and in the multiway system.** [CORRECTED
2026-10-26, evening: this holds for runs whose *head* redex stays the only redex; one-redex evolutions that descend into
arguments for ever are a separate class (Theorem DK).] These are the
terms where Wolfram's weak and strong notions coincide trivially, and none of them computes beyond a linear counter.
This removes the most order-robust candidates for a universal construction. It does not settle terms with several
redexes, which is where the open core lies. The core of Theorem UR-R (entry into the Φ-regime and Φ-states for ever) is now
machine-checked in Lean 4 (lean/URCore.lean); Theorem UR-C's classification step is still a hand proof with
machine-checked data.

## Update 2026-10-26, night (parallel evaluation) — read first
**Still not solved; nothing submitted or published.** Gap (4), other orders: parallel (ReplaceAll) evolution now has an
exact lazy machine (Lemma LZ) and a first exact theorem for a run that differs from its head run (Theorem PL), and an
automatic prover (Theorem LP-par, with an extension for comb families that keep evolving) certifies 86 of the 150
census-sample parallel runs, each checked against 400,000 passes. Most of the rest time out; binary-type counters would
need a parallel call prover. This is per-term evidence for one more order, not a general theorem, so
the overall picture is unchanged: no universal construction in any order studied, and no complete disproof in reach.

## Update 2026-10-26, end of the overnight run — read first
**Still not solved; nothing submitted or published.** New since the update below:
* **Gap (3):** Conjecture R″ in its *morphic* form is FALSE (Theorem NM: the square runs' window words are not morphic,
  by Lemma S and the certified opcode words). Only R″_PUP remains — which is what Proposition UB needs, and which every
  proved run satisfies. Coverage: every run of every random hunt is now proved — 25–40 leaves 150/150 (base-3 call
  recursion, E82), 40–80 leaves 100/100 (binary call recursion via the template-driver fallback, E81; one loop after an
  opcode-encoding bug fix, E83), 80–160 leaves 100/100 (E85), 160–320 leaves 100/100 (E86), 320–640 leaves 100/100 (E87) — 850 of 850 endpoints; census counters 148/152 (147 kept through the RESUME hardening, E78, plus the four countdown counters of Theorems CD, CD2, CD3 and the last counter of Theorem NS, E88–E93: 152/152)
  and sample 150/150.
* **Gap (4), other orders:** Theorem UR — a 10-leaf term with a unique redex at every step for ever, so all evaluation
  orders (and the multiway system) coincide on it; such terms exist from 10 leaves on and all those found (109 up to
  14 leaves) are linear counters. Leftmost-innermost (call-by-value): either the evolution descends for ever (the
  outside freezes; bounded-prefix detectors decidable) or it contracts at a fixed depth (1, 13, 40 root-level cases with
  9, 10, 11 leaves, mostly evaluating arguments on the way; all look like linear counters). Parallel evaluation: still
  open (nested evolutions, E75/E76).
* Nothing here changes the overall picture: no universal construction exists in any order studied, and no complete
  disproof is in reach.

## Update 2026-10-26, latest (loop prover; multiway topology) — read first
**Still not solved; nothing submitted.** New since the gap map below:
* **Gap (3), leftmost-outermost:** a third automatic prover (Theorem LP: loop lemma LB + cycle lemma LC with comb tokens;
  multi-loop cycles, combs in any list position, loop variables in several places) brings the census sample to 150/150
  non-counter endpoints proved exact (with 147/152 counters, an estimated ≥ 98% of all 18,326 hnf-free endpoints of
  terms ≤ 12 leaves; every proof with strong numerical cross-checks), and all 100 endpoints of a random sample of
  13–16-leaf terms (E68). Every proof is a per-term symbolic certificate with numerical cross-checks. The five unproved counters
  show regular nested structure (countdown epochs (m−1) m (m−2) m ⋯; exact doubling) — no candidate for a
  non-morphic run. Conjecture R″ itself remains open in general: per-term certificates do not prove it for all terms.
* **Multiway topology (Proposition MW, PROVED):** (size, −leaf depth) increases strictly at every S-step, so multiway graphs
  are DAGs, sizes diverge along every infinite evolution, and reachability is decidable; reduction-closed multiway
  detectors coincide with one Gross–Knuth evolution (cofinality, cited); and no reachability-respecting decoder can mirror
  nondeterministic branching (true of every confluent system, SK included). So the strong definition adds no new route
  beyond gaps (2) and (4): branching must be represented as data and read from one (parallel) evolution or from Böhm trees.

## Map of the remaining gap after Proposition CF (2026-10-26, latest) — read first
A universal emulation needs a non-universal detector that signals the emulated machine's halting. Split detectors by
what they read:
1. **Halting = the evolution stops / the multiway graph is finite.** Impossible for every order (Theorem T: all-or-
   nothing and decidable).
2. **Halting = a control-flow event** (control reaches a designated continuation; more generally any property of the
   head-normal-form events / Böhm tree). Identical under every head-fair order and in the multiway system (Proposition CF,
   Böhm-tree invariance). Non-universality here ⇔ decidability of the corresponding Böhm-tree properties of S-terms —
   the finite S-models (C6, C8, path models) are EXPERIMENTALLY SUPPORTED, their termination halves unproved.
3. **Halting read from intermediate syntax with a bounded window**, leftmost-outermost order: non-universality ⇐ effective
   Conjecture R″ for (k, d)-windows, all k — and only in its weaker form R″_PUP (window words effectively profinitely
   ultimately periodic, Carton–Thomas; square nested runs found at 25–40 leaves may not be morphic, E73) (Proposition UB, corrected 2026-10-26). Per term this is now settled for every
   proved run — whole-list certificates (Corollaries LP′, CA′) give R″_{k,d} for every k — but not for all terms. R″ is PROVED for the families of Theorems BC, BC2, TC, K, K′ and supported by every
   census and sample, but open in general.
4. **Intermediate syntax under other orders** (e.g. parallel evaluation): only here does the order matter, and only
   through syntax and timing (never control flow). In general nothing proved; per term: runs that coincide with their
   head runs (CA-par, K0, UR) and one that does not (Theorem PL, via the lazy machine of Lemma LZ); all 150 census-sample
   parallel runs look loop-like (E96).
So a complete disproof needs: the finite-model termination proofs (2), effective R″ (3), a syntax theory for other orders
(4), and an argument that Wolfram's notion of a non-universal detector falls under 1–4. A universality proof needs a
construction in 2, 3 or 4 — and the capability map, the barrier lemma and Proposition CF show that every mechanism found
so far is a fixed recursion in its control flow.

## Update 2026-10-26, later (rules re-checked; binary counter solved; call algebra) — read first
**Still not solved.** What changed:
* **Rules, from Wolfram's 2021 announcement (re-read 2026-10-26):** an emulation needs an encoder, detector and decoder
  that are not themselves universal (e.g. they halt in bounded time). Two definitions are left open: *strong* — the
  multiway system (all reduction paths) emulates a multiway Turing machine; *weak* — some path (evolution order) performs
  any given computation. No evaluation order is prescribed. Preferred form: Wolfram Language code implementing the
  solution; an abstract proof is accepted; non-universality or 'intermediate degree' also resolves the challenge. The
  announcement asks for Wolfram Language code or an abstract proof — but **correction (later re-read):** the prize home
  page (combinatorprize.org) requires the solution 'in the form of a technical research paper, suitable for publication',
  a full proof, the original work of the submitter(s) with all relevant contributors named, no anonymous submissions.
  The strong definition, re-read, asks the multiway system to emulate the multiway system of a nondeterministic Turing
  machine — Proposition MW(e) shows a reachability-respecting decoder cannot do that for any confluent system (S or SK).
* **Consequence (asymmetry):** a universality proof may pick one evolution order — leftmost-outermost is enough — so a
  universal construction in head runs would suffice. A non-universality proof must cover every evolution order (and the
  multiway system) and every non-universal encoder/detector/decoder; our obstruction theorems are leftmost-outermost
  results restricted to their hypotheses, and the Böhm-tree models are order-independent only for halting signals that
  are Böhm-tree properties (Böhm trees are invariant under reduction by confluence). Intermediate-state detectors under
  other orders are not covered by anything we have.
* **Binary counter solved exactly (Theorem BC, PROVED):** the head run of SSS(SS)S(SS(SS)) (and four other terms) is an
  explicit infinite binary counter with morphic opcode word — Conjecture R″ holds for it.
* **Counters in every base (Theorems TC, K, PROVED):** a 23-leaf term's head run is an exact ternary counter, and for
  every base μ ≥ 2 an explicit S-term's head run is an exact base-μ counter; the base is a unary gadget inside a fixed
  driver (data in code). Still fixed recursions — morphic — so they support Conjecture R″ rather than universality.
* **Order independence of control flow (Proposition CF, PROVED):** which argument receives control (and, up to
  conversion, with what) is the same under every head-fair evaluation order, by Church–Rosser. Parallel evaluation's
  time-to-data channel therefore changes only intermediate syntax and timing, never control flow. For a disproof this
  reduces the 'other evaluation orders' gap to one question: can a non-universal detector extract universal power from the
  order-dependent intermediate syntax? For a universality proof via a non-standard order, the universal behaviour would
  have to live in that syntax, not in the control flow.
* **Bridge (Proposition UB, PROVED conditionally):** if every head run's bounded-window word is effectively morphic
  (Conjecture R″), then no leftmost-outermost emulation with a bounded-window finite-state detector is universal
  (Carton–Thomas: MSO of morphic words is decidable). So the leftmost-outermost part of a disproof is exactly R″, and a
  leftmost-outermost universality construction is exactly a counterexample to R″.
* **Call algebra (Theorem CA, PROVED):** S alone has composable subroutine calls — SS and seq(A_1..A_k) — realising every
  fixed recursion scheme (k-ary counters for every k). This is the first positive control-flow ingredient without K or I,
  but calls are data-blind; universality would need a driver that builds new levels in a data-dependent way. No such
  driver is known.

## Update 2026-10-26 (prover vs disprover rounds) — read first
**Still not solved; no submission-ready result in either direction.** Inside one infinite leftmost-outermost head run
(the regime no earlier theorem covered) we now have, all audited:
* universality side: exact loops with data-driven zero tests (the sawtooth), exact clean transfer passes, and a two-level
  'pump' loop whose rounds move one unit from a head counter into a unary supply ((k, n) ↦ (k−1, n+1)) — but every loop
  found runs only finitely many rounds or never transfers; no reload that rebuilds a counter from the transferred value
  has been found (bounded searches);
* non-universality side: Theorem U* (the fuel-free invariant holds forever, through zero tests), Corollary W (nothing is
  written cleanly behind a live control in fuel-free runs), the frame lemma, the access lemma, Lemma G1 and the placement
  lemma — together they explain every blocked design: material flows from a target's head down into its supply; it can
  flow back only through writes, and each write leaves a stale copy above the new value.
* What a prize needs and we lack: a complete universal construction (all ladder rungs) or a proof that covers every
  admissible evaluation order and encoding. Neither is in reach on current evidence; the honest estimate of completing
  either within this project's sessions is low.
* Roadmap that the pieces now fit (leftmost-outermost evaluation only): (1) head runs → full re-execution — every
  growth of a counter beside a live control needs a re-read copy (U*, Corollary W, write-pass theorem; Theorem O for
  leftmost paths); (2) full re-execution = Böhm-tree dynamics of closed terms (the executed material is closed; its
  output is hnf components, cf. 'Strategic picture' in STATUS.md); (3) Böhm-tree dynamics are regular (Conjecture C9;
  proved pieces: Q10, LP1, P2, Q′, Q″). (1) is largely proved for counter-style designs but not for arbitrary designs;
  (3) is the deep open part. Even all three together would cover one evaluation order, not Wolfram's full notion.

## Bottom line (2026-10-25)
**Not solved.** The evidence now points clearly to **non-universality** (H1), and the remaining gap is sharply
localised. One loophole is not covered at all: universality that is visible only to decoders reading node syntax *and*
whose halting cannot be made to diverge. Everywhere else, what is missing are proofs of the finite-model conjectures (termination
arguments). A universality proof would need an explicit construction inside that loophole, and every structural result
found so far works against one.

## What a universal emulation would have to look like (all PROVED unless marked)
| Route to universality | Status |
|---|---|
| Halting = no normal form / no head normal form | impossible: both decidable (Waldmann; Padovani) |
| Program-holds-registers designs, tag-system appends, junk-free queues | impossible (Lemmas 8–10, Theorem J, Prop. M) |
| Two counters at bounded cost per instruction (any layer shapes, exact checkpoints) | impossible (Theorem O, audited) |
| Two counters at unbounded cost | must re-read a counter (almost) completely per growth step; transfers cost Ω(a²) (Theorem O) |
| Halting signalled by Böhm-tree shape: no ⊥ / finite tree / leftmost or rightmost path finite | impossible **if** the learned finite models are correct (C6, C8, …); each verified on every term ≤ 19 (or ≤ 14) leaves |
| Any decoder (even syntactic) with halting that can be made to diverge, along leftmost/rightmost/LO paths | impossible **if** the corresponding path property is decidable (Proposition R, audited; learned models for all three paths: 36/19/204 classes). "Can be made to diverge" (modularity) is an assumption, not derived from universality |
| Remaining loophole | emulations whose halting can't be made to diverge, read only by syntactic decoders, in the full re-execution regime |

## New results of this project that a referee could check
* **Theorem P2 (PROVED):** Böhm-tree finiteness of S^{k+3}(SSS)(SS) holds iff k is even — S-terms count mod 2 (refutes
  our earlier counter-freeness conjecture C4).
* **Theorem O (PROVED; independently audited, gaps repaired):** no bounded-cost two-counter simulation.
* **Finite S-models (EXPERIMENTALLY SUPPORTED, exhaustive to 19 leaves):** productivity (39 classes, answers BEKW Question 5
  conjecturally), Böhm-tree finiteness (131), leftmost path (36), rightmost path (19); only parity counting occurs (C10).
* **Propositions Q, Q′ (PROVED modulo BEKW Question 10):** one half of the productivity and finiteness models.

## What would actually win the prize
1. **Non-universality route (most promising):** prove the termination halves of the finite models — Q10 (head
   normalisation automaton; Padovani's proof in *A Lambda Calculus Satellite* Ch. 7 may already contain it — not
   accessible to us), C6/C8 completeness — then Proposition R gives non-universality for every emulation whose halting can
   be made to diverge. Remaining argument needed: that Wolfram's notion of universality implies this modularity.
2. **Universality route:** an explicit construction in the full re-execution regime that cannot be made to diverge at
   halting. No candidate exists; all searches negative.

## Recommended next steps
* Obtain Satellite Ch. 7 (Padovani): if it proves BEKW Fig. 14, Propositions Q/Q′ become unconditional halves.
* Write the results up as a paper and ask experts (BEKW authors, Manzonetto, Padovani) to check them before any
  submission — **only with your approval**.

## Update — direct attack on the termination core (2026-10-25)
* **Padovani's proof is not accessible** (homepages checked; the Satellite is a commercial book). Question 10 remains the
  linchpin of the conditional results.
* **Ranking-function route (BEKW's own suggestion) — negative, certified:** no labelled size-potential (two or three
  label types) certifies Q10 for all terms, although such potentials fit every actual run up to 11 leaves.
* **Intersection types — exact reformulation:** Q10 ⟺ soundness of a recursive type assignment derived from M35.
* **Fast-or-never for leftmost paths — linear form refuted:** finite leftmost paths can have length k²+3k+3 (explicit
  family); any computable bound would be equivalent to decidability, so no shortcut.
* **Evidence keeps strengthening:** the LO-evaluation path model (204 classes) agrees with brute force on every term up to
  18 leaves.
* **Honest status:** the remaining step is a genuine research problem (termination of S-term head reduction and of
  Böhm-tree path exploration on the predicted classes). The fastest realistic unblocker is Padovani's chapter.

## Update — standard termination toolbox exhausted on Question 10
Linear potentials with two or three label types (LP-certified impossible), recursive intersection types (exact
reformulation only), RPO with M35 labels (precedence self-loop), an engine lemma (fails: divergence is non-local),
leftmost-path pushdown and linear fast-or-never (both refuted). Lemma 13 (PROVED; its timing part conditional on C2): a
minimal counterexample to Q10 must read every argument-internal subterm that is not size-minimal in its class (within
2|t| steps if C2 holds). **The missing ingredient is a genuinely new termination argument — most likely the
one in Padovani's chapter (A Lambda Calculus Satellite, College Publications 2022, ISBN 978-1-84890-415-6, Ch. 7).**
Seven Böhm-tree properties now have finite models (latest: branching infinity, 423 classes, exact to 16 leaves).

## Update — typing route to Question 10, and audit 3 (2026-10-25)
* The user-supplied Satellite excerpt is the FSCD 2023 summary already on file: it confirms Padovani's theorem
  (termination of head reduction is decidable) but contains no proof. Nothing changes in the assessment.
* **New exact tool (Lemma 14, PROVED):** non-idempotent intersection types characterise head normalisation of S-terms,
  and each head step lowers the derivation weight by one — even for recursive types. This is the first certificate
  format that can tell an opened copy of a duplicated argument from a passive one (the obstruction that killed every
  potential-based attempt).
* **But (Proposition T, PROVED):** no finite set of such types certifies Q10; the search fails on the same seven classes
  as every earlier attempt. A certificate would need schematic (tail-polymorphic) types — open.
* **Conjecture C12 (bounded re-opening, exhaustive to 13 leaves):** terminating runs use each part of the term at most
  2 (application) / 4 (leaf) times, diverging runs dozens of times; implies a linear-time decision procedure.
* **Audit 3 (Lemma 13, Proposition S):** both correct with fixes, now applied; the quadratic leftmost-path family is now
  proved for all k, and Proposition S is retitled (it relies on Padovani's theorem and does not avoid a decidability proof).
* **Prize status unchanged: not solved.** The decisive missing piece is still a termination argument for the finite
  models (or Padovani's chapter), plus the modularity gap in Proposition R.

## Update — BEKW Question 10 PROVED (2026-10-25, Theorem Q10, independently audited)
* **What changed.** The linchpin of every conditional result is now a theorem: an S-term has a head normal form iff its
  class in the 35-element model (BEKW Fig. 14) is not ⊥. The proof is elementary plus certified finite checks (a
  rank argument on the model, "only S has class s", and an acyclic graph of 8,329 tail-chain states); an adversarial audit
  re-derived every finite fact with its own code and validated about 5 million concrete transitions. It also gives a
  linear-time decision procedure for head normalisation (an independent proof of Padovani's theorem).
* **Now unconditional:** Propositions Q and Q′ (the soundness half of the productivity model C6; the "infinite" half of the
  Böhm-tree-finiteness model C8), Proposition Q″ (the "infinite" halves of the leftmost- and rightmost-path models), and
  R10′ (head normalisation cannot count).
* **Still open on the non-universality route:** the other halves — "⊥_P ⇒ not productive", "F_fin ⇒ finite Böhm tree",
  "leftmost/rightmost path model says finite ⇒ path finite". The same certificate idea does not close them directly:
  Böhm-tree paths lack the rank monotonicity of head runs, and concrete paths run nested counters (E35). Then the
  modularity hypothesis of Proposition R, and evaluation orders other than head/leftmost-outermost (Wolfram's "weak"
  universality allows any evaluation order), remain.
* **Prize status: not solved.** This is a genuine research result (an open question of Barendregt–Endrullis–Klop–Waldmann
  answered), worth writing up and showing to experts — with your approval only.
