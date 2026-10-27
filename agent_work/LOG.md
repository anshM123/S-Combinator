# PROOF STATUS (non-universality agent) — maintained at the top; last update 2026-10-27 02:45 EDT
Target: a complete proof that S is not universal in Wolfram's sense (every evaluation order, every non-universal
encoder/detector/decoder).  Map follows the main agent's split (PRIZE_ASSESSMENT.md 'Map of the remaining gap').
Labels: DONE = proved (hand) or machine-checked; OPEN = not proved.  [file pointers in brackets]
A. Definitional reduction (Wolfram's 'non-universal decoder' falls under classes 1-4 below) ... OPEN (informal only)
   [PRIZE_ASSESSMENT.md 'Rules'; Proposition MW excludes the strong/multiway definition for reachability-respecting
   decoders: DONE, main agent, PROOF.md].
B. Class 1, halting = evolution stops / multiway graph finite ......................... DONE (Theorem T, Waldmann)
   [PROOF.md].
C. Class 2, halting = control-flow event / Boehm-tree property (order-independent by Prop. CF) ... OPEN: termination
   halves of the finite models C6, C8 and the path models; soundness halves DONE (Q, Q', Q'') [PROOF.md].
D. Class 3, bounded-window syntax under leftmost-outermost: needs effective R''_PUP for ALL head runs (Prop. UB) ... OPEN.
   D0. Per-term certificates for every census/sample/hunt run; classes: unique-redex runs (UR-R/UR-C, Lean core),
       counters BC/TC/K/K', loops LP, nested loops NL ............................ DONE (main agent) [PROOF.md, lean/]
   D1. Data-flow obstructions in head runs, generic phase model (this agent) ........ DONE, machine-checked:
       OC1 (only S is transparent) [agent_work/lean/OC.lean]; RC, OT (ordered data never hand over a clean transfer)
       [lean/OT.lean]; OTD (frozen atoms allowed), FH (frozen-headed level blocks the predecessor) [lean/OTD.lean];
       SL (single-level data: P-elements glued onto Y are predecessor-headed) [lean/SL.lean]; canonical chain bound
       (single-level transfer => next phase cannot iterate without re-execution) [lean/CANON.lean].
       Scope: generic (opaque) data, Church-style phases; these do NOT by themselves prove R''_PUP for any new class.
   D2. Multi-level data.  (a) Theorem MSL in STRICT form (P-elements glued onto Y are prefixed by one of the
       datum's own levels or have only such P-arguments) and Lemma AB (|P| >= 3 is absorbing) ... DONE,
       machine-checked [agent_work/lean/MSLS.lean (strict + generous), lean/MSL.lean, lean/AB.lean].
       (b) Phase 3 is never a proper transfer (for data built from phase-2 outputs) ... OPEN in general
       (computationally certified: exhaustive <= 11 leaves, 115k + 367k targeted data, 70k random).
       DONE parts: Lemma YD (machine-checked [lean/YD.lean]: bare y glued down early => no proper transfer; bare-S
       outer wrapper); REPLAY relation (machine-checked [lean/REPLAY.lean]: a phase-2 transfer reached from the
       self-application list args w ++ [w, y, x.y, r] is replayed as a REEXEC of phase 3); FH (p-headed wrapper);
       CANON (single-wrapper handler => at most one more transfer phase); Corollary AB-c (hand: >= 3 C-elements =>
       no p'-front); case (i) (hand: last C-element disposed onto P').  OPEN: case (ii) (sigma_C path) for live
       handlers; a replay relation covering all real phase-2 outputs.
   D3. 'Re-execution of a frozen value is call-like' => R''_PUP ...................... OPEN (conjectural target)
E. Class 4, other evaluation orders (parallel, innermost, multiway paths) .............. OPEN in general; Prop. CF
   (control flow order-independent) DONE; per-term parallel certificates (main agent) [PROOF.md, STATUS.md].
F. Decoders reading unbounded parts of terms (not windows) ............................. OPEN (not covered by UB).
Bottom line: NOT SOLVED.  No step above that is OPEN is close to a complete proof; D1 narrows the possible
universal mechanisms (they must re-execute frozen values), it does not exclude them.

# INTERIM 04:00 (non-universality agent; written 2026-10-27 02:30 EDT)
Bottom line: NOT SOLVED.  No complete proof of non-universality exists; nothing below claims one.
New since the coordinator's 'go for the money' message (all in agent_work/; labels as in the entries below):
1. MACHINE-CHECKED  Lemma AB (absorbing P-count): once >= 3 elements contain the live atom (and no x, y, r), there
   are >= 3 for ever and no such element is ever glued onto an input-containing element.  [lean/AB.lean]
2. MACHINE-CHECKED  Theorem MSL (multi-level SL): for every phase-2 datum K.(d2.(...(dk.p))) (closed wrappers,
   frozen atoms allowed) every P-element glued onto a Y-element is level-prefixed or has only level-prefixed
   P-arguments ('good'); hereditary form for all reachable lists.  [lean/MSL.lean: msl_glue, msl_main]
   Consequence: every P-wrapper of a proper phase-2 handler is good.  This is the 'extend SL's invariant to
   several levels' option of the Phase-4 request.  (It also holds verbatim in phase 3, so by itself it does not stop
   a Church chain.)
3. PROVED (hand)  Lemma YD (bare y glued down before any y-node other than x.y exists => no proper transfer);
   Corollary AB-c (in phase 3, >= 3 C-elements => no p'-front and no call ever); together with FH these dispose of
   the outer-wrapper classes 'bare S' and 'p-headed' and of all phase-3 data that release >= 3 C-elements.
4. MACHINE-CHECKED modulo renaming (CANON + FH)  a single-wrapper phase-2 handler (77% of real cases <= 11 leaves)
   makes phase 3 single-level, so at most one more transfer phase follows.
5. COMPUTATIONALLY CERTIFIED  'phase 3 is never a proper transfer' on 115,442 further phase-2 data (K <= 7 leaves,
   tails with wrappers <= 4 leaves; 5,086 proper phase-2 transfers) and the exhaustive <= 11 range.
6. EXPERIMENTALLY SUPPORTED  the mechanism: (a) good general phase-3 shapes transfer only when the wrapper is a
   c-comb; (b) the REPLAY RELATION: phase 3 replays phase 2 under theta = (w -> p', p -> c), turning phase 2's
   transfer into a REEXEC; exact replay covers 38/836 single-wrapper cases; a general replay is OPEN.
Still OPEN for item D of the map: D2(b) 'phase 3 never proper' in general (needs a general replay or a C-material
invariant; case (ii) = sigma_C path); D3 're-execution is call-like'; and items A, C, E, F (untouched by this agent).
Files: lean/AB.lean, lean/MSL.lean (new, compile with Lean 4.35 core, no sorry); msl_inv.py, target3.py,
inner_forms.py, outer_forms.py, goodhits.py, goodhits2.py, target_hits.py, p3events.py, p3events2.py, p3trace*.py,
replay_check.py, replay2.py, replay3.py (scripts; results quoted in the LOG entries of 2026-10-27 01:35-02:30).

# agent_work LOG (construction agent)

Conventions: list [a,b,c|R] => args(a) ++ [c, b.c | R]; numerals N_1 = SS, N_{n+1} = SS.N_n (= PROOF.md's n-bar).
Labels: PROVED / COMPUTATIONALLY CERTIFIED / EXPERIMENTALLY SUPPORTED / CONJECTURAL / REFUTED.

## 2026-10-26 (start)
* Tooling: agent_work/hm.py (hash-consed head machine with atoms), bt_survey.py, act_rules.py.
* EXPERIMENTALLY SUPPORTED (all S-terms <= 9 leaves, 6 atom args): the head of the stuck front of T x1 x2 ... xn is x1 or
  x2, never x3+.  PROVED (barrier argument, same as PROOF.md barrier lemma with a closed prefix of any length): in
  args(T) ++ [x1, x2 | r], x1-headed elements are never destroyed and must stay above x2 until x2 is popped as the third
  element of a step whose second element is x1-headed; then two barriers sit above r.  So r is never popped before an
  x1/x2-headed front.  (Known in substance: PROOF.md 'Barrier lemma'.)
* Activation rules (act_rules.py): [T, u, v | r] always reaches a list over {v, Z = u.v} and constants: u never
  appears except inside u.v (= PROOF.md capability (a)).
* COMPUTATIONALLY CERTIFIED (agent_work/parity_search.py, parity_10.txt): for every 1-hole context C with <= 10 leaves,
  the outcome of the head run of C[N_n] J K L for n = 1..8 (which opaque atom heads the stuck front, or 3000-step
  budget) changes at most once in n: only zero/threshold tests, no parity-like dependence.  (65,000+ contexts.)
* Searching Church-style transfer contexts (agent_work/transfer_search.py): F with [F[a], x, b] ->* [a, x', G[b]] and
  reverse [G[b], y, c] ->* [b, y', F[c]].  Up to 9 leaves: every F whose stuck front is exactly a has G[b] = b (no
  increment).  Size 11 running.
* COMPUTATIONALLY CERTIFIED (transfer_search.py 11, transfer_11.txt): among 1-hole contexts F <= 11 leaves, 8,174 have
  [F[a], x, b] ->* [a, x', G[b], ...] with G a clean 1-hole context (b once, no x); typical: F = S(S a)c gives
  G[b] = c.b (PROOF.md's head-style nest).  For NONE of them does G satisfy the reverse transfer
  [G[b], y, c] ->* [b, y', F[c], ...].  So no self-sustaining two-way Church-style transfer pair (F, G) <= 11 leaves.
* COMPUTATIONALLY CERTIFIED (loop_state_search.py 7 4): numeral loop L_k = N(k).s.(H.S) (activating L_k.w1.w2 gives the
  body list args(H) ++ [S, s, L_{k-1}.s, w1, w2, ...], so the 'state slot' w1 is NOT glued to the loop continuation);
  no body H <= 7 leaves with dispatcher s <= 4 leaves turns the state t into a clean f(t) in the next state slot
  (414 'bare M' fronts, 150 with M inside w1, 16 with w1 = t).
* COMPUTATIONALLY CERTIFIED (transparent_search.py 11): S is the only closed term <= 11 leaves whose activation rule is
  [v, u.v] ++ (closed junk).  So the S-absorption queue  [S, acc, S, S, ..., S, X] ->* [X, acc.S^m.X]  (clean packing
  of a stack of S's into acc's top layer; unpacking by activation) exists only for the one-letter alphabet {S}: unary
  queues, no 2-letter tag-system queue from 'transparent' symbols.  (S(SS)S has rule [v, Z, v(Sv)Z]: transparent but
  pushes v-junk, which breaks the queue.)
* Observation (PROVED, elementary): the left comb D_n = S^n.D_0 is a Church numeral for the 'Fibonacci swap'
  (u, v) -> (v, u.v) (Lemma R' type-1 layers); the head of v_n alternates, so [D_n, J, K] with D_0 = S is stuck at a
  K-headed front for n even and J-headed for n odd: parity of a comb IS testable (unlike numerals). Not new in
  substance (Lemma R').
* PROVED (Lemma OC, occurrence counting).  Let nu(L) = number of occurrences of an atom v in the list L.  A head step
  [a, b, c | R] => args(a) ++ [c, b.c | R] changes nu by exactly +nu(c) (a's occurrences all lie in args(a); b's move
  into b.c; c's are doubled).  So nu never decreases, and grows exactly when the third element contains v.
  Corollary OC1: for every closed T != S whose generic run [T, u, v | r] gets stuck, the stuck list contains >= 3
  occurrences of v (after T's opening v sits at position |args T| + 1 >= 2 with u.v directly below it and only closed
  elements above; positions of deeper elements drop by at most 1 per step, so before any v-element can reach the front
  some step has v or u.v as its third element).  Hence S is the ONLY closed term with rule [v.w, (u.v).w', closed...]
  (w, w' closed): the transparent/emitter searches (<= 11 leaves) hold at every size.  (Known in spirit: PROOF.md's
  'pass rule' [S, T, S] -> [S, T.S] is agent U's pump; this lemma says the pump's alphabet cannot be enlarged.)
* PROVED (Lemma NC, numeral chains).  If an element with spine [S, N(m), y, s, w...] (= N(m+1).y.s.w..., m >= 1) is
  activated with inputs (e1, e2), then two steps later y is activated with inputs (N(m).y, s), with
  w..., e2, e1.e2 below.  The only new element containing N(m) is N(m).y.s (u only as u.v).  So along a numeral
  chain the handler y always receives the SAME second input s; a chain cannot carry a changing state in its inputs.
  Information between iterations can only travel through the stack below, which y's activation cannot see
  (barrier lemma) unless y's rule makes s the front with <= 1 element after it.
* COMPUTATIONALLY CERTIFIED (transfer_graph.py 9): 'clean Church-transfer edges' G -> H between 1-hole contexts
  (generic run of [G[b], x, y | r] stuck at a BARE b front whose v-input is H[y], y once, no x/b/r): 823 edges among
  contexts <= 9 leaves; every target H is [] (70 cases) or a right comb of closed terms over the hole (c.[],
  S(S[]), ...), and NO target has a clean outgoing edge: no chain G -> H -> K, no cycle.  Mechanism (sketch): in a
  'pred-last' datum c.b the predecessor-carrying element sits directly ABOVE the handler y after opening, and y can be
  transformed only after the pred element has been glued below it or consumed, so the pred is never activated with a
  transformed handler as its clean v-input.  (Matches PROOF.md Theorem U 'straight-line only' and the write-pass
  theorem; a proof for all sizes is NOT done.)
* NOTE (process hygiene): two of my searches (compare_search 9, parity2 7 7) grew to 4.5 GB / 7.6 GB because hm.py
  hash-conses every node forever; killed (my PIDs 68356, 119696) and hm.py got mark()/truncate() for per-run memory
  release.  Relaunched with truncation.
* COMPUTATIONALLY CERTIFIED (parity2.py 7 7, parity2_77.txt): for all closed x, y <= 7 leaves (38,809 pairs) the
  outcome of [N_n, x, y, J, K, L] for n = 1..10 changes at most once in n (25,481 constant, 13,328 one threshold, 0
  others).  With Lemma NC this supports CONJECTURE (numeral inertness): for every closed context C the outcome of
  C[N_n] is eventually constant in n.
* PROVED + MACHINE-CHECKED (Lean 4 core, agent_work/lean/OC.lean, compiles with
  ~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean OC.lean; no sorry; axioms propext, Quot.sound only):
  `occL_step` (Lemma OC), `oc1` (Corollary OC1: for closed T with args T != [], every stuck list reachable from
  args T ++ [v, u.v, r] has >= 3 occurrences of v), `no_transparent` (no closed T != S has a stuck rule
  [v.w..., (u.v).w'..., rest..., r] with w, w', rest closed).  Model: terms S | var n | app; step only on S-headed
  fronts (atom-headed front = stuck).
* PROVED (Lemma RC, right combs; hand proof, all sizes).  Let C be a list of terms containing none of the atoms
  x, y, r, and run the generic machine from C ++ [y, x.y, r].  Then every term that ever occurs (as a list element or a
  subterm of one) and contains y exactly once and neither x nor r has the form d1.(d2.(...(dm.y))) with every d_i free
  of x, y, r (m >= 0).  Proof: two invariants, preserved by every step (case split on which of a, b, c contain an atom
  of X = {x, y, r}): (I1) the list is (X-free elements)* ++ (X-containing elements)*; (I2) every S-headed X-containing
  element has spine (X-free args)* ++ (X-containing args)*, recursively.  The only new term of a step is b.c; if it
  contains y once and no x, r then c does (b above c, so b cannot be X-containing while c is X-free by (I1)) and b is
  X-free; induction.  Consequence: the only clean (y-once, x-free) transformations a closed code can apply to its
  v-input are LEFT multiplications by x,y,r-free terms (writes c.y); y.c, (y.c).d, etc. are impossible.  (Claim 1 of
  the transfer-graph analysis; it explains why all 220 targets found by tg_chains.py are right combs.)
* COMPUTATIONALLY CERTIFIED (tg_chains.py 10): 2,559 clean transfer edges among 1-hole contexts <= 10 leaves, 652
  proper (target != hole), 220 distinct targets, all right combs; each target's own edge is none/dirty/junk-front or
  clean-to-identity: NO proper -> proper chain.  [Superseded: Claim 2 is PROVED for all sizes below as Theorem OT,
  Lean-checked in lean/OT.lean.]  Was CONJECTURAL for all sizes (Claim 2: a datum of right-comb shape
  d1.(...(dk.b)) never hands its predecessor a properly transformed handler).  Proof sketch (incomplete): a proper
  pure-y V is created only by a step [a, d, q] with a, d closed, at which moment every b-containing element lies
  below q; a persisting element is never overtaken except by consuming it; the remaining gap is V-copies released
  later from containers.

## 2026-10-26 (later): Theorem OT — ordered data cannot drive a proper transfer (PROVED, all sizes)
Setting: atoms b (a datum inside the code), x, y, r (generic inputs / tape); X = {x, y, r}, A = {b} u X.  A term is
*proper pure-y* if it is d1.(d2.(...(dm.y))) with m >= 1 and every d_i closed (no atoms).  A term t is *ordered*
(w.r.t. an atom set) if every S-headed subterm of t that contains one of the atoms has spine args
(atom-free)* ++ (atom-containing)*.  Right combs d1.(...(dk.b)) with closed d's are ordered w.r.t. b.
**Theorem OT.** Let G[b] be a closed-except-b term, ordered w.r.t. b.  In the generic run from [G[b], x, y, r]
(atom-headed fronts are stuck), no list element containing b ever lies above a list element that is proper pure-y.
In particular the run never gets stuck at a b-headed front (bare b or b.w...) whose second or third element is a
proper pure-y term: a datum of ordered shape can never hand its predecessor a properly transformed handler.
*Proof.* (I1) the list is (A-free)* ++ (A-containing)*; (I2) every S-headed A-containing element is ordered w.r.t. A.
Both hold after the first step (args(G[b]) ordered, then y, x.y, r) and are preserved (case split on which of a, b, c
are A-containing; the only new term is b.c; released args come from an ordered element) — this is PROOF.md's F1/F2
invariant of Theorem U with data = A-containing.  Call a term *bad* if some subterm has spine args s_i, s_j (i < j)
with s_i containing b and s_j proper pure-y; call the list bad if it contains a bad term or a b-containing element
above a proper pure-y element.  The first list is not bad (its only y-terms are y and x.y).  Suppose L is not bad and
L -> L' = args(a) ++ [c, b'.c] ++ R (front a, second b', third c).  A proper pure-y element V of L' is
 (i) new: V = b'.c with b' closed and c pure-y (Lemma RC: the left factor of a pure-y product is X-free; V b-free
     forces b' closed).  By (I1) a (above the closed b') is A-free, so everything above V in L' (args(a), c) is
     b-free.
 (ii) released from a: if a spine arg of a before V contained b, a would be a bad term of L.  So all of args(a) above
     V are b-free.
 (iii) old (V in R or V = c copied): elements above V in L' are old elements above V (b-free since L not bad), args(a)
     with a above V (b-free), c and b'.c only if both b', c lie above V (b-free).  An element of L below V cannot
     get above V without V being at position 1 or 2, i.e. consumed.
 New bad terms: b'.c is bad only if (c proper pure-y and some spine arg of b' contains b — then b' contains b and lies
 above c in L: L bad) or b' or c is bad in L.  Released args and copies are old terms.  So L' is not bad.  ∎
*Checks.* ordered_check.py (random contexts 3–16 leaves, 400 steps, every step checked): ordered contexts 12,691
runs, 0 bad pairs; unordered contexts 21,929 runs, 2,434 with bad pairs (e.g. S(S b)c, PROOF.md's head-style nest,
which is NOT ordered: spine [S b, c]).
*Consequences.* (1) With Lemma RC: every clean single-occurrence value that code writes from a generic datum is a
right comb over it, hence ordered; so a datum produced by code can never itself drive a proper Church-style transfer.
Proper transfers need an unordered datum (b before a closed arg, like S(S b)c), which code cannot write from a
generic datum — such data must be present in the initial term.  This is the all-sizes form of the transfer-graph
finding (no proper -> proper chains) and a structural explanation of Theorem U's 'straight-line only'.
(2) Scope: generic (opaque) data, single occurrence of each datum, closed wrappers, 'clean' hand-off (the handler
value is a whole list element).  NOT covered: values containing a datum twice (duplicating writes, as in the binary
counter's levels), values mixing two data, non-generic data whose code interleaves with the handler's, and
full re-execution designs in general.
* MACHINE-CHECKED (2026-10-27, agent_work/lean/OT.lean, 632 lines, Lean 4.35 core, no sorry; axioms propext,
  Classical.choice, Quot.sound): `ot_main` (Theorem OT exactly as stated above: G S-headed, ordered, no y; along the
  run from args G ++ [y, x.y, r] no b-containing element ever lies above a proper pure-y element), `ot_no_transfer`
  (corollary: no reachable list f :: w :: v :: rest with f containing b has w or v proper pure-y), and `rc_main`
  (Lemma RC for closed code G: every subterm of every reachable element with one y and no x, r is y or proper pure-y).
  Together: closed code writes only right combs over its v-input (rc_main); right combs over a datum are ordered; an
  ordered datum never hands its predecessor a properly transformed handler (ot_main).  Hence Church-style clean
  transfer chains have length <= 1 beyond the unordered (initial-term) data — all sizes.
  Compile: ~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean agent_work/lean/OT.lean (and OC.lean).
* COMPUTATIONALLY CERTIFIED (compare_search.py 9 5, compare_9.txt): all 134,142 two-hole contexts with <= 9 leaves
  (holes included) filled with numerals N_a, N_b (a, b = 1..5): every outcome table is a function of
  (min(a, t1+1), min(b, t2+1)) with t1, t2 <= 2 — no comparison (a < b) or other two-numeral interaction.
* COMPUTATIONALLY CERTIFIED (dirty_chain.py 9): allowing DIRTY transfers (the handler wrapper may contain the old
  predecessor, which is then frozen as an opaque atom c_i for the next phase), chains over all 1-hole contexts <= 9
  leaves: 17,226 with 0 proper phases, 344 with 1, 6 with 2, none with 3.  Every 2-chain ends because the next datum is
  headed by (or must open) a frozen old predecessor, e.g. S(S#)(S(SS)S) -> S(SS)S# -> c1(S c1)# -> [headless]: to
  continue, the old value must be RE-EXECUTED — exactly PROOF.md's 'full re-execution frontier'.  (EXPERIMENTALLY
  SUPPORTED that this is the only continuation; not a theorem.)

## Summary of this agent's session (2026-10-26/27)
Construction side: no 2CM simulation, no transfer loop, no parity/comparison gadget for numerals, no non-PUP run found.
Every attempted primitive (parity of numerals, comparison of two numerals, Church transfer pairs, loop state slots,
transparent/emitter symbols, clean and dirty transfer chains) failed in exhaustive bounded searches, and three of the
failures are now theorems for all sizes (OC1, RC, OT; Lean-checked) plus Lemma NC (hand proof).  Positive
observations: left combs ARE parity-testable data (Fibonacci swap), and 2-step dirty transfer chains exist; both are
regular mechanisms.  Most promising next step (construction): data whose phase-2 datum is headed by the frozen old
value (c1(S c1)#) — i.e. designs where the old counter is re-executed as code — combined with comb parity; or
(obstruction): extend Theorem OT from closed wrappers to wrappers containing the old predecessor (dirty transfers),
which would show every transfer chain of bounded depth ends in re-execution.

## 2026-10-27 Phase 3 (coordinator request): dirty wrappers, duplication, the re-execution regime
* Starting point (PROVED by inspection of the OT proof): Theorem OT holds verbatim with 'closed' replaced by
  'A'-free' for A' = {p, x, y, r} — frozen atoms (old predecessors) may occur anywhere in code and wrappers.  The
  I1/I2 invariants only need atom-headed fronts to be stuck, which holds for frozen atoms too.  So a datum that is a
  right comb over the current predecessor p with p-free wrappers (frozen atoms allowed) can never make a proper
  transfer whose wrappers are all p-free: every proper transfer from such a datum is DIRTY w.r.t. the CURRENT p.
  (To be machine-checked in agent_work/lean/OTD.lean.)
* COMPUTATIONALLY CERTIFIED (chain3.py 11 5): all 23,713 right combs over p with CLOSED wrappers and <= 11 leaves as
  phase-2 data; every proper phase-2 transfer (p-headed stuck front, proper right comb V over y at position 2 or 3)
  turned into its phase-3 datum D3 = V[y -> p, p -> c1]; phase 3 outcomes: 1,319 re-execution (stuck at a c1-headed
  front), 168 handler call (y-front), 1 x-front, 220 p-front without proper V, 3 budget; ZERO proper phase-3
  transfers.  (Phase 2 itself: 10,558 p-front without proper V, 7,330 y-front, 2,283 x-front, 1,993 budget.)
* COMPUTATIONALLY CERTIFIED (chain_rand.py 1 20000 12 3): 20,000 random phase-2 data (1-3 random closed wrappers of
  <= 12 leaves): 1,007 proper phase-2 transfers, 0 proper phase-3 transfers.
* PROVED (Lemma FH, frozen-headed level blocks the predecessor).  Let D = d1.(d2.(...(dk.p))) and suppose some
  wrapper d_i is headed by a frozen atom c.  Then in the generic run of [D, x, y, r] no p-headed element exists before
  a c-headed element has been at the front.  Proof: let L_i = d_i.(...p) (head c).  Until a c-headed front occurs,
  every occurrence of p in the list lies inside an occurrence of L_i: steps only glue elements (subterms preserved) or
  release the spine arguments of an opened element; an element whose spine contains L_i's spine is L_i-headed hence
  c-headed and is never opened without a c-headed front; any other opened element releases L_i whole or keeps it
  inside an argument.  A p-headed element has a p occurrence at its head, and a subterm containing the head
  occurrence of an element is headed by p, but L_i is headed by c.  ∎  So a dirty transfer whose wrapper is
  p-HEADED (class P) is the last transfer before re-execution: the next datum then has a c-headed level.
* COMPUTATIONALLY CERTIFIED (chain_rand.py 2 20000 25 5 and 3 30000 8 6): 50,000 more random phase-2 data (wrappers
  up to 25 leaves / up to 6 wrappers): 2,021 proper phase-2 transfers, 0 proper phase-3 transfers.
* EXPERIMENTALLY SUPPORTED (wrapper_skel.py 11): the wrapper lists of all proper phase-2 transfers from closed-wrapper
  right combs <= 11 leaves fall into 32 skeletons (closed subterms abstracted to K); every dirty wrapper is built from
  right combs over p with closed wrappers (K(Kp), K(K(Kp)), ...) and bare p by application, e.g. p(Kp),
  Kp(K(Kp)), K(Kp)(K(K(Kp))): the dirty wrappers are COPIES OF THE DATUM'S OWN LEVELS (and of p), glued together.
* IMPORTANT NEGATIVE CONTROL (phase3_skel.py 2 60000 12): phase-3-SHAPED data built from the skeletons with random
  closed parts K (c frozen) DO make proper transfers (30 of ~60,000 samples containing c), e.g.
  D3 = SS(c1)(S(SS)p) -> V = c1(S(SS)p)y (whose phase-4 datum is c1-headed, blocked by Lemma FH).  So 'phase 3 is
  never proper' is NOT a consequence of the wrapper SHAPES alone; it depends on how phase 2 copies its own levels.
  Mechanism seen in examples ('replay'): a phase-2 dirty wrapper is a copy of a datum level L_i; in phase 3 the
  frozen copy L_i[p -> c] is opened above the new predecessor, and its code replays on (c-remnant, next level, y)
  what it did on (p-remnant, y, x.y) in phase 2 — a phase-2 transfer becomes a phase-3 re-execution of c.
* COMPUTATIONALLY CERTIFIED (phase2_general.py 10): GENERAL ordered phase-2 data (all S-headed ordered 1-hole contexts
  <= 10 leaves: 16,795): 1,155 proper phase-2 transfers; phase 3: 935 re-execution, 188 p-front without proper V,
  85 handler call, 0 proper.
* MACHINE-CHECKED (agent_work/lean/OTD.lean, 580 lines, no sorry): (a) `ot_main` re-proved with `closed` meaning
  'free of p, x, y, r' (atoms var n, n >= 4, are frozen old predecessors and may occur anywhere; a frozen-headed
  front is stuck).  This is Theorem OTD: an ordered datum never has a p-containing element above a proper right comb
  over y whose wrappers are p-free (frozen atoms allowed) — every proper transfer from phase 2 on is DIRTY w.r.t.
  the CURRENT predecessor.  (b) `fh_main` / `fh_rcomb` (Lemma FH, axioms: propext only): if some level of the datum
  d1.(...(dk.p)) is headed by a frozen atom, no p-headed list element ever occurs: the datum can make no transfer
  of any kind (proper, dirty or identity) before it is stuck at a frozen-headed front.
* COMPUTATIONALLY CERTIFIED (single_level.py 12): all closed K <= 12 leaves (~82,500), single-level data K.p: 3,104
  proper transfers with 4,407 proper V's; EVERY proper V has a p-HEADED wrapper (0 exceptions).
* PROVED (corollary of OTD, all sizes): in every proper transfer from an ordered datum, the INNERMOST wrapper (the one
  applied directly to y) contains p.  Proof: let w_j be the innermost p-containing wrapper (one exists by OTD); if
  j < m, U = w_{j+1}.(...(w_m.y)) is a proper right comb with p-free wrappers, and at the step that formed w_j.U the
  p-containing w_j sat directly above U — a bad pair, impossible by OTD's invariant.  So j = m.
* COMPUTATIONALLY CERTIFIED: for single-level data K.p (closed K <= 11 leaves) the innermost wrapper of every proper
  transfer is p-HEADED (1,452 of 1,452).  With Lemma FH this would give: after a transfer from a single-level datum
  (the canonical case: an F-type source S(S a)K transfers into K-wraps, whose layers are single-level), the next
  phase can never iterate without re-execution.  PROOF STATUS: partial.  The natural invariant INV-Q ('every non-
  p-headed P-element has a p-headed element above it or a p-headed P-element below it'; regions CL* P* Y*) implies
  the step lemma 'a P-element glued onto a Y-element is p-headed', and its preservation is proved in every step case
  except (front P, second P, third Y), where it needs 'the front's P-arguments are p-headed'.  That extra fact held in
  all 1,864 such steps of 19,209 random single-level runs (invq_fast.py, ppy_cases.py) and INV-Q held in ~1M steps,
  but no invariant proving it was found (q_struct.py shows Q-elements with non-p-headed P-args do occur elsewhere).
* (Task 2, duplication) OBSERVATION/PROVED: Theorems OT, OTD and FH never assumed a single occurrence of the datum:
  the hypothesis is only that the datum is ORDERED.  Binary-counter-style levels such as U_m = S S P_m (S (S S W P_m))
  and P_{m+1} = S U_m (P_m twice) are ordered w.r.t. P_m, so OT/OTD/FH apply to data written by duplicating writes
  verbatim.  Lemma RC2 (PROVED, same invariants as RC): every term containing y (any number of times) and no x, r
  that occurs in the generic run of closed code from [..., y, x.y, r] has all its maximal closed subterms in FUNCTION
  position (left children): code can left-multiply and self-apply y-terms, never apply them to closed terms.
* COMPUTATIONALLY CERTIFIED (multi_y.py 10): duplicating HANDLER values (y >= 2 times, no x, r) at p-headed stuck
  fronts of ordered data <= 10 leaves: 1,399 cases, ALL y-headed and containing p (e.g. y(py)); as next-phase data
  they are predecessor-headed, i.e. an immediate identity transfer.  No p-free or S-headed duplicating transfer.
* COMPUTATIONALLY CERTIFIED (comb_rounds.py 5 3000; task 4 probe): for J, K <= 5 leaves and 5 small Z, the depth of
  the first NEW left comb at the front of [S^n S, J, K, Z] (n = 2..11) is never a non-affine function of n: no
  parity-dependent comb rounds from small gadgets.  (A hand design would need comb WRITES with stale copies that
  are themselves re-executed — a full re-execution design; not attempted further.)

## Task 3: the regime that remains — definition and target (2026-10-27)
**Generic phase model (precise).**  A *phase* is a datum D: a term over S, one live atom p (the current
predecessor) and frozen atoms c_1, c_2, ... (earlier predecessors), with no x, y, r.  Its *phase run* is the generic
head run of [D, x, y, r] in which every atom-headed front is stuck.  Outcomes: TRANSFER (p-headed stuck front;
the new handler is the element at position 2 or 3, a right comb over y by Lemma RC), CALL (x-, y- or r-headed front),
REEXEC(c_i) (c_i-headed front: the old value c_i would be executed), DIVERGE.  A *Church chain* is a sequence of
phases with D_{j+1} = V_j[y -> p, p -> c_j] (V_j the new handler of a proper TRANSFER of phase j).
**What is now known.**  (i) OTD (machine-checked): from an ordered datum every proper TRANSFER is dirty w.r.t. the
live p, and its innermost wrapper contains p.  (ii) FH (machine-checked): a datum with a frozen-headed level never
reaches TRANSFER of any kind.  (iii) COMPUTATIONALLY CERTIFIED: in every tested chain the third phase is never a
proper TRANSFER (it ends in REEXEC, CALL or identity transfer); for single-level phase-2 data the innermost wrapper
is p-headed, so (ii) applies.  So, within the generic phase model, an infinite computation that keeps transforming
data must infinitely often end a phase in REEXEC.
**Definition (re-execution regime).**  An infinite head run is in the *re-execution regime* if every cover of it by
generic phases (each phase = maximal stretch on which the run equals the phase run of its datum with all values
built in earlier phases frozen) has infinitely many phases ending in REEXEC.  Runs NOT in this regime are, after
finitely many phases, sequences of phases ending in TRANSFER/CALL only; by (i)-(iii) their proper transfers stop
after a bounded number of phases (proved when the chain passes through a p-headed wrapper, certified otherwise), so
from then on every phase is a CALL or an identity transfer — data-blind iteration (PROOF.md: calls carry no data).
**Target for a final impossibility theorem (CONJECTURAL).**  Re-execution is call-like: when a frozen value V is
re-executed with inputs (u, v), the stretch until a u- or v-headed front (barrier lemma) acts on (u, v) by a generic
rule of V (a list over {v, u.v} and sub-values of V, cf. act_rules.py) drawn from finitely many PARAMETRIC rule
schemes per run — as for the levels of the binary counter (Theorem CA) and numerals (Lemma NC).  If true, every
infinite head run is a composition of finitely many parametric rule schemes, which is the shape of the certified
mechanisms (calls, loops, nested loops) and would give R''_PUP.

## 2026-10-27: Theorem SL (single-level data) — PROVED by hand (completes the canonical-chain bound)
Setting: K free of p, x, y, r (frozen atoms allowed); generic run from args(K) ++ [p, y, x.y, r] (= [K.p, x, y, r]
after one step).  Classes: CL = free of p,x,y,r; P = contains p, not x,y,r (PH = p-headed P, Q = other P);
Y = contains x, y or r.
Invariants: (O) list = CL* ++ P* ++ Y* and every S-headed element is ordered (OTD's I1/I2 for the atom sets
{p,x,y,r} and {x,y,r}); (INV-Q) every Q-element has a p-headed element above it or a PH element below it;
(T) if P has exactly two elements, one of them is PH and every Q one among them has only PH P-arguments;
(YS) S-headed Y-elements have no P spine arguments.
Step lemma: if a step has its 2nd element in P and its 3rd in Y, the 2nd is PH (else INV-Q needs a p-headed element
above it — only the front, which would be stuck — or a PH element below it in P — none, it is the last P-element).
Preservation, by the classes of (front a, 2nd b, 3rd c), non-decreasing in CL < P < Y by (O):
(CL,CL,CL), (CL,CL,Y), (CL,Y,Y): P unchanged or empty, b.c in CL or Y with CL/Y args (YS).
(CL,CL,P) insertion b.c below the P-top c: c is PH or (by INV-Q, no p-headed above it) has a PH witness below,
  which is also below b.c; if P = [c] then c is PH and (T) holds for [c, b.c].
(CL,P,P) glue: b.c below c; witnesses move with b (b.c keeps b's head) or stay (c copied); (T): from [b, c] to
  [c, b.c]: if b is Q then c is PH and P-args(b.c) = P-args(b) ++ [c] are all PH.
(CL,P,Y): P = [b], b PH by the step lemma; P becomes empty and stays empty (CL and Y elements release no P args).
(P,P,P): the Q front a has a PH witness below it; a's released P-args land above that witness (b -> b.c keeps the
  head, c is copied); witnesses of b.c and c as in (CL,P,P).
(P,P,Y): P = [a, b] exactly; by (T) b is PH and all P-args of a are PH, so after the step P consists of PH
  elements only.  (T) is preserved: 2-element P-regions arise only from 1-element ones by insertion, from
  2-element ones by glue, or from (P,P,Y) — checked above; 3+ element regions never shrink to 2.
Hence every P-element ever glued onto a Y-element is p-headed.  With the OTD corollary (the innermost wrapper of a
proper transfer contains p, and it was glued onto y): **every proper transfer from a single-level datum K.p has a
p-headed innermost wrapper**, and by Lemma FH the next phase's datum (with p frozen) can never activate its
predecessor: no TRANSFER of any kind before REEXEC.
Checks: claimT_check.py (14,397 random runs, 489,414 steps: INV-Q, (T) and the step lemma never violated);
single_level.py (exhaustive K <= 12) and the 1,452 innermost-wrapper cases agree.
**Corollary (canonical Church chains).**  An F-type source S(S a)K transfers clean K-wraps (layers K.[]): single-
level phase-2 data.  So the chain source -> K-wrap target -> next counter has at most two transfer phases before a
frozen value must be re-executed (in the generic phase model).  PROVED by hand (SL) + machine-checked parts (OTD,
FH); Lean formalisation of SL itself NOT done.
* MACHINE-CHECKED (agent_work/lean/SL.lean, 790 lines, Lean 4.35 core, no sorry; axioms propext, Classical.choice,
  Quot.sound): Theorem SL.  `sl_main`: for K free of p, x, y, r (frozen atoms allowed) and every list reachable from
  args K ++ [p, y, x.y, r], every subterm w.q of every element with w in P (contains p, no x, y, r) and q in Y
  (contains x, y or r) has w p-headed.  `sl_step_lemma`: a step gluing a P-element onto a Y-element glues a
  p-headed one.  The Lean invariant SLI is the hand proof's invariant in the simplified form discovered while
  formalising: the list is C ++ Pl ++ Yl (closed / P / Y), Pl is empty or contains a p-headed element (equivalent
  to INV-Q, since a witness above or below always exists when one exists at all), Claim T for |Pl| = 2, plus
  orderedness and the hereditary predicates hy (S-headed Y-subterms have no P arguments) and gl.
* MACHINE-CHECKED ingredients + 3-line hand glue => **Corollary (canonical Church chains, all sizes).**  If the
  datum of a phase is single-level, K.p with K free of p, x, y, r, then the innermost wrapper of every proper
  transfer is p-headed (OTD's ot_main: it contains p, so it is a P-element glued onto y; SL's sl_main: it is
  p-headed), hence the next datum has a frozen-headed level and by FH (fh_rcomb) its generic run never produces a
  p'-headed element: the next phase cannot iterate before re-executing a frozen value.  In particular an F-type
  source S(S a)K -> K-wrap target -> anything chain makes at most two transfer phases without re-execution.
* MACHINE-CHECKED (agent_work/lean/CANON.lean, 1,288 lines = SL.lean + OTD's OT/FH part + 180 new lines; no sorry;
  axioms propext, Classical.choice, Quot.sound): `canonical_innermost` — for a single-level datum K.p (K free of
  p, x, y, r), whenever the generic run reaches f :: w :: V :: rest with f containing p and V = d1.(...(dm.y))
  (m >= 1, all d_i free of x, y, r), the innermost wrapper dm is p-headed.  The proof combines ot_main (no
  p-containing element above a proper pure-y), a new hereditary invariant nb2 (no subterm w.U with U proper pure-y
  and w containing p), and sl_main (P-elements glued onto Y are p-headed).  The remaining link to the next phase
  is pure renaming: V[y := p', p := c] has the c-headed level dm[p := c] and its outer wrappers contain no p', so
  `fh_rcomb` applies.  So the canonical-chain corollary is machine-checked up to that renaming step.
  (Stated for V at position 3, the v-input of the predecessor's activation; position 2 is analogous, not stated.)

## Phase 3 summary (2026-10-27)
(1) Dirty wrappers: OTD (dirty is necessary; innermost wrapper contains the live predecessor), FH (frozen-headed
level blocks), SL + canonical_innermost (single-level data: the innermost wrapper is predecessor-headed) — all
machine-checked.  Hence: for chains whose transferring phases have single-level data, at most one dirty transfer
before re-execution; in the canonical Church chain (F-type source -> K-wrap target), at most two transfer phases.
General multi-level phase-2 data: phase 3 never proper is COMPUTATIONALLY CERTIFIED only (exhaustive <= 11 leaves
right combs, all ordered contexts <= 10 leaves, 70,000 random); the multi-level case produces S-headed dirty
wrappers (copies of the datum's own levels) and shape alone does not block phase 3 (negative control), so the
missing proof must use the 'replay' relation between phase-2 code and the copied levels.
(2) Duplication: OT/OTD/FH need only orderedness, so data written by duplicating writes (binary-counter levels) are
covered; RC2 (hand proof) characterises duplicated written values; duplicated handler values at transfer outcomes
are handler-headed (certified <= 10 leaves).  SL/canonical_innermost assume the datum is single-level K.p (p once).
(3) The re-execution regime: defined above (generic phase model; REEXEC phases); target conjecture stated.
(4) Construction probe with comb parity: nothing found in small searches (comb_rounds.py).

## 2026-10-27 Phase 4 (coordinator request): multi-level data and the replay relation
* Starting observation (PROVED by inspection of SL): a multi-level datum d1.(L2), L2 = d2.(...(dk.p)), runs EXACTLY
  as SL's single-level run with predecessor atom X1 := L2, up to the first X1-headed front (L2 is never opened
  before; an element containing L2 as a spine argument releases it whole).  So SL applies to every SUB-PHASE of a
  multi-level phase: P-elements (containing X1, no x, y, r) glued onto Y during sub-phase 1 are X1-headed.  The
  multi-level run is a NESTED chain of single-level sub-phases; the transition step (opening X1 = L2 at the front)
  glues its two inputs e1.e2 and can glue a non-headed P-element onto Y (e.g. [L2, S.L2, y] -> [p, y, (S.L2).y]
  for D2 = SSS(Sp)): that is where S-headed dirty wrappers come from.
* COMPUTATIONALLY CERTIFIED (ml_wrappers.py 11): all multi-level phase-2 data (right combs over p with closed
  wrappers, k >= 2 levels, <= 11 leaves: 16,795 data, 1,245 proper V's): the innermost wrapper is p-headed (124),
  LEVEL-PREFIXED, i.e. L_j.u... for an exact copy of a datum level L_j (235), or S-headed with every p-containing
  spine argument p-headed or level-prefixed (886); nothing else.  This is the nested-SL picture: within sub-phase
  j SL forces X_j-headed (= L_{j+1}-prefixed) glued elements; at a transition step (opening L_{j+1}) the glued input
  is X_j-headed or has only X_j-headed P-arguments (Claim T).
* REFUTED (naive invariant H3): 'phase 3 never glues a P'-element (contains p', no x, y, r) onto a Y-element'.
  Counterexample: D2 = SSS(Sp) -> V = S(Sp)y -> D3 = S(S c)p'; first step [S c, p', y] -> [c, y, p'.y]: the
  p'-headed P'-element p' is glued onto y, and the very next front is c (REEXEC).  Over all multi-level data <= 11
  leaves (phase3_glue.py + outcome scan): 245 phase-3 runs glue a P'-element onto a Y-element; of these 201 end in
  REEXEC, 39 call the handler y, 1 the handler x, and 4 reach a p'-front whose position 3 is the bare y (the wrapped
  y lies deeper, at position 4); 1,000 runs never glue (784 REEXEC, 216 identity p'-fronts).
* COMPUTATIONALLY CERTIFIED (phase3_fronts.py 11): at EVERY p'-headed stuck front of a phase-3 run (220 such fronts),
  positions 2 and 3 hold P'-elements or the bare y, and the bare y is still present (at position 3: 146, 4: 56,
  5: 18); the wrapped y, when it exists, lies deeper.  Mechanism seen: the dirty wrapper's frozen arguments
  (C-elements: contain c, no p'/x/y/r) sit directly above p' after the innermost level is opened (orderedness puts
  them last); they cannot be opened down to c without REEXEC (c-headed elements never disappear), so the code glues
  them onto p'-elements, creating 'buffers' C0.P' (non-p'-headed P'-elements) between the p'-headed elements and y.
* REFUTED (naive phase-3 invariants, buf_check.py 11): (QP) 'the P'-region is empty or contains a p'-headed element'
  fails trivially before the innermost level of D3 is opened (P' = [D3]); (BUF) 'if the C-region is empty, the
  P'-bottom is not p'-headed' fails: D3 = S(SS)(S c)p' reaches [ (S c)p', p'((S c)p'), y, ... ] at step 3 (C empty,
  P'-bottom p'-headed) — the run then opens the buffer (S c)p', releasing c at the front (REEXEC) one step later.
* MSL candidate invariants in phase 2 (msl_check.py; LP* = prefixed by a datum level L_j, j >= 2, or p-headed):
  on all 428 multi-level right combs <= 8 leaves, MQ ('P-region nonempty => contains an LP* element'), MT ('|P| = 2 =>
  non-LP* members have only LP* P-arguments') and GL ('P glued onto Y is LP* or has only LP* P-arguments') never fail;
  the auxiliary guess MA (arguments glued onto LP* elements are LP*-good) FAILS (2 runs, e.g. S(S(SSS))S(Sp) at step
  6: L2.(S L2).(S(S L2)(L2(S L2)))).  N = 10 run in progress.
* EXAMPLE (phase-3-shaped datum NOT produced by any tested phase-2 run): D3 = S(S(SSc)).p' runs
  [S(SSc), p', y, xy, r] -> [SSc, y, p'y, ...] -> [S, c, p'y, y(p'y), ...] -> [p'y, c(p'y), y(p'y), xy, r]: a p'-headed
  front with the proper y-term c(p'y) at position 2 (u-input) and y(p'y) at position 3 (v-input).  So 'no p'-front
  above a proper y-term at position 2' is false for general phase-3-SHAPED data; any proof must use the shape of
  phase-2 outputs (its wrapper S(S(SS p)) has a non-level-prefixed P-argument, which MSL's GL excludes).  Decision:
  'proper transfer' from now on means a proper right comb at POSITION 3 (the v-input of the predecessor's next
  activation); position 2 is the u-input and is only available glued to position 3.
* COMPUTATIONALLY CERTIFIED NEGATIVE CONTROL, position 3 (p3shape_pos3.py 1 60000 14): phase-3-SHAPED single-level
  data D3 = W.p' (W random <= 14 leaves, contains the frozen c, ordered) DO make proper transfers at POSITION 3:
  4 of ~12,500 samples, e.g. W = S(S(S(SSS)(c1))) stuck at [p'y, S(p'y), c1(p'y), y(p'y), ...] (v-input c1(p'y)).
  So 'phase 3 is never proper' (certified for real phase-2 outputs) is false for general phase-3 shapes even with the
  position-3 definition; its proof MUST use the shape of phase-2 dirty wrappers (here w = S(S(S(SSS) p)) has a
  non-level-prefixed P-argument, excluded by the MSL candidate GL).
* PROVED (Lemma AB, absorbing P-count; hand proof, general).  In any generic run whose lists have the form
  CL* ++ P* ++ Y* (CL free of the live atom p and of x, y, r; P contains p but no x, y, r; Y contains x, y or r) and
  whose S-headed P-elements are ordered, if the P-region ever has >= 3 elements it has >= 3 elements for ever, and no
  later step glues a P-element onto a Y-element.  Proof: with k >= 3 P-elements a step's classes are non-decreasing;
  (CL,CL,P) adds one, (CL,P,P) keeps k, (CL,P,Y) needs k = 1, (P,P,P) opens a P-front which releases >= 1
  P-argument (it contains p in some spine argument, which then contains no x, y, r), giving k - 1 + #P-args >= k;
  (P,P,Y) needs k = 2; a Y-front needs k = 0.  A P-onto-Y glue needs P inside the first two positions.  ∎
  Corollary: a proper transfer (p-headed front, proper y-term at position 2 or 3) can occur only while |P| <= 2, and
  every wrapper glued onto y was glued while |P| <= 2.
* PROVED (phase 3, single-level D3 = W'.p', case analysis; hand proof, not audited): with regions CL* C* P'* Y*
  (C = contains the frozen c, no p', x, y, r): (a) the C-region never empties by opening (an S-headed C-element
  releases >= 1 C-argument; a c-headed one is stuck), only by gluing its bottom element onto the P'-top (a 'buffer'
  C0.X, P'-count +1) or onto the Y-top (only when P' is empty); (b) every p'-headed front needs C = CL = empty;
  (c) while C is nonempty no closed element is directly above the P'-top, so no insertion t.X happens.
  Case (i), the last C-element is disposed onto P': then |P'| >= 2 from then on until a buffer is opened, opening a
  buffer re-releases C-elements directly above the P'-top, |P'| = 1 never coexists with C = empty, and the Y-top stays
  the bare y; so every p'-front has the bare y at position k'+1 <= 3 or |P'| >= 3: NO proper transfer.  Case (ii), the
  unique P'-element is glued onto the bare y during the opening of a C-front (sigma_C), after which P' stays empty
  for ever: here proper transfers are possible for general shapes (the control above), via 'y glued down, then
  C-disposals onto the exposed p'-headed Y-element'.  So the open part of 'phase 3 is never proper' is exactly case
  (ii), and it needs the MSL shape of the phase-2 wrapper.
* MACHINE-CHECKED (agent_work/lean/AB.lean, Lean 4.35 core, no sorry; axioms propext, Classical.choice,
  Quot.sound): Lemma AB.  `ab_step` / `ab_run` / `ab_no_glue`: for lists C ++ Pl ++ Yl (C free of atoms 0..3 —
  frozen atoms allowed, so phase 3's C-elements count here —, Pl contains p = var 0 and no x, y, r, Yl contains
  x, y or r) with all elements ordered and |Pl| >= 3, every later list keeps |Pl| >= 3 and no step ever glues a
  P-element onto a Y-element.
* (bookkeeping) msl_check.py 10 and absorb_check.py 10 hit their 30-minute timeouts without output (killed by
  `timeout`, exit 124); superseded: AB is machine-checked, and the exact MSL invariant is checked below.
* PROVED (Theorem MSL, multi-level SL; hand proof 2026-10-27 ~02:00, Lean formalisation in progress).
  Lv = right combs over p with closed wrappers (Lv p; Lv l, d closed => Lv d.l).  LP(e): some left-spine prefix of
  e is in Lv ("level-prefixed"; includes p-headed).  good(e): LP(e) or every P spine argument of e is LP.
  Setting: K closed, l in Lv, generic run from args(K) ++ [l, y, x.y, r] (= one step after [K.l, x, y, r]; every
  multi-level phase-2 datum d1.(d2.(...(dk.p))) is K.l).  **Claim: every step that glues a P-element b onto a
  Y-element glues a good b; hereditarily, every subterm w.q (w in P, q in Y) of every reachable list has good w.**
  Invariant (while |P| <= 2; once |P| >= 3 Lemma AB takes over for ever): regions CL* P* Y*; every S-headed subterm
  has spine args CL* P* Y* (OTD's I1 plus 'ordY': no non-Y argument after a Y argument); MQ: P = [] or some
  P-element is LP; MT: |P| = 2 => each non-LP P-element has only LP P-arguments; MA (hereditary): every subterm
  l.u with l in Lv and u in P has good u; GM (hereditary): every subterm w.q with w in P, q in Y has good w.
  Key facts: (1) opening an LP front a = (d.l').u1...un releases args(d) (closed) ++ [l', u1..un], and l' is LP;
  if exactly two P-args result then a = l.u1 and MA gives good(u1); a non-LP good front releases only LP P-args;
  so after any P-front opening MQ and MT hold.  (2) An S-headed Y-front a has its P-arguments inside its maximal
  non-Y prefix s, and s.q is a subterm (q in Y), so GM gives good(s) and (1) applies.  (3) Cases with |P| <= 2:
  (CL,CL,CL), (CL,CL,Y), (CL,Y,Y): P unchanged / empty.  (CL,CL,P), P = [c] (LP by MQ): new P = [c, b.c],
  P-args(b.c) = [c] all LP.  (CL,P,P), P = [b, c]: new P = [c, b.c]; MQ via b LP => b.c LP, or c LP; MT: non-LP c
  has LP P-args (old MT), non-LP b.c has P-args P-args(b) ++ [c] (b non-LP so c LP); new node b.c: if b in Lv then
  c is good (LP or MT): MA kept.  (CL,P,Y), P = [b]: b LP (MQ) => good: GM kept; P empty after.  (P,P,Y),
  P = [a, b]: b good by MQ+MT (GM kept), new P = P-args(a) by (1) (a good by MQ+MT).  (P,Y,Y): a LP by MQ, (1).
  (Y,Y,Y): (2).  Transitions to |P| >= 3 hand over to AB (no P-onto-Y glue ever again, so GM persists).
  COMPUTATIONALLY CERTIFIED (msl_inv.py: the exact invariant, all 1,429 / 4,861 multi-level right combs with
  <= 9 / <= 10 leaves, S-headed, 300-400 steps): never violated (173 / 875 runs enter the AB regime).
  Extended: N = 11 (all 16,795 multi-level right combs <= 11 leaves, 300 steps; 3,761 enter the AB regime, 470
  hit the budget inside the small regime): never violated.
* MACHINE-CHECKED (agent_work/lean/MSL.lean, 1,205 lines = AB.lean + 610 new lines; Lean 4.35 core, no sorry;
  axioms propext, Classical.choice, Quot.sound): **Theorem MSL** exactly as stated above, for K closed and l in Lv
  where `closed` = free of p, x, y, r (FROZEN ATOMS ALLOWED in K and in the wrappers of l).
  `msl_glue`: every reachable list a :: b :: c :: R with S-headed a, b in P, c in Y has good b.
  `msl_main`: every element of every reachable list satisfies GM (every subterm w.q, w in P, q in Y, has good w).
  `msl_first_step`: [K.l, x, y, r] steps to the start list args K ++ [l, y, x.y, r] when K is S-headed.
  Proof = the invariant MInv := (MS ∨ SegBig) ∧ GM: MS is the small-P invariant of the hand proof (10 cases in
  `ms_step`), SegBig is Lemma AB's regime (`ab_step`), and `LP_open` / `open_P` / `open_Y` are fact (1)-(2).
  Consequence (hand glue, same as CANON for SL): every P-wrapper of a proper phase-2 transfer handler (each was
  glued onto a y-term) is good; by OTD the innermost one is a P-wrapper.  NOTE the theorem allows frozen atoms in
  the wrappers, so it ALSO applies verbatim to phase 3 (D3 = V[y:=p', p:=c] is again K'.l' with c frozen):
  MSL alone does not stop a Church chain; what is still OPEN is that phase 3 cannot make a proper transfer, which
  must use the specific c-shapes w[p:=c] of good phase-2 wrappers w (the negative controls show that general
  phase-3-shaped data DO transfer).
* (bookkeeping) case_split.py 2 80000 14 also hit its 30-minute timeout without output; superseded by the
  event statistics below.
* COMPUTATIONALLY CERTIFIED (target3.py 7 4 9, beyond the exhaustive range): D2 = K.T with K closed S-term <= 7
  leaves and T a right comb over p with wrappers <= 4 leaves (T <= 9 leaves): 115,442 phase-2 runs, 5,086 proper
  transfers at position 3; their phase-3 runs: 3,688 REEXEC, 1,268 p'-fronts with position 3 NOT proper, 115 call y,
  15 call x; **no proper phase-3 transfer**.
* EXPERIMENTALLY SUPPORTED (p3events.py ex 10 / t 6 4 8; 352 + 962 phase-3 runs from real phase-2 outputs): the
  events used by the general-shape counterexamples DO occur in real phase 3 — sigma_C (C-front opened while the
  only P'-element is glued onto the bare y: 41 / 318 runs), the bare y glued down from the Y-top (26 / 166), C onto
  Y (12 / 140) — yet every p'-front has the bare y (44 / 235) or a P'-element (15 / 13) at position 3.  So no
  single forbidden event explains 'phase 3 is never proper'; a proof must track the C-material through these
  steps.  Typical real run: opening the c-level releases the BARE c (args(d_k.c) ends in c), which is glued onto
  the Y-top (c.y) and resurfaces as a REEXEC front (p3trace.py 10 4).
* EXPERIMENTALLY SUPPORTED (goodhits.py 11 300000 13): among 48,973 random phase-3-shaped single-level data W.p'
  whose phase-2 preimage w = W[c:=p] is GOOD (generous Lv), 22 make a proper position-3 transfer; in all 19
  distinct hits w is itself a right comb over p with closed wrappers (e.g. w = S(S(S(SS)(SS)p))), so strict
  goodness would need w = L_j, a datum level glued onto y as the innermost wrapper.  target_hits.py 8 2 (D2 =
  K.T and K.(d.T), T = each hit's w, K <= 8, d <= 2 leaves; 35,682 runs): only 5 proper phase-2 transfers, none with
  innermost wrapper T, no proper phase-3 transfer.  Mechanism in the hits: sigma_C, then the bare y is glued down
  onto p'.y under a C-front, then the bare c (from the c-level) is glued onto p'.y: stuck at [p'.y, s, c.(p'.y)].
* COMPUTATIONALLY CERTIFIED (inner_forms.py ex 11 / t 6 4 8): innermost wrapper w of every real proper position-3
  phase-2 transfer, against the datum's own levels (strict): PH (p-headed; 110 / 100), LEV (w = L_j exactly; only
  with >= 2 wrappers: 53 / 6), LPU1 (w = L_j.u, ONE extra argument; 112 / 121), SLP (not LP, all P-args strictly LP;
  667 / 735); never LPU with >= 2 extra arguments, never OTHER.  Phase 3: REEXEC, CALL or non-proper p'-front.
* PROVED (Lemma YD, y glued down early; hand proof, general).  In a generic phase run the only y-node (subterm d.y
  with y the right child) initially is x.y; new y-nodes arise only by gluing an element onto the BARE-y element.
  If the bare y is glued down (y at position 2) while x.y is the only y-node, the bare y never reappears as a list
  element (y is never a spine argument of an S-headed subterm afterwards) and every y-node has d = x, so no proper
  y-comb (y once, no x, r) ever exists: NO proper transfer in that phase.  Corollary: a datum S.U with U S-headed
  (bare S as outer wrapper) never transfers properly ([U, y, x.y] glues y onto x.y at step 2).  This disposes of
  the outer wrapper class 'S' of multi-wrapper handlers (outer_forms.py: 64 cases <= 11 leaves).
* PROVED (Corollary AB-c; hand proof, via Lemma AB with the frozen c as the live atom and p', x, y, r as inputs).
  For phase-3 data D3 = V[y:=p', p:=c] from ordered phase-2 runs, every S-headed subterm of D3 has its spine args
  ordered (free of c,p',x,y,r)* (C)* (containing p',x,y or r)*, so the phase-3 lists are CL* C* I* and Lemma AB
  applies to (C, I): once the C-region has >= 3 elements it keeps >= 3 for ever, hence the front is never an
  I-element: NO p'-front and NO call ever; the phase ends in REEXEC or diverges.  (Lean: AB.lean applies after
  merging p' with x by an atom renaming; the renaming lemma is not formalised.)  E.g. LPU1 / SLP innermost wrappers
  whose phase-3 image releases >= 3 C-arguments at once.
* MACHINE-CHECKED modulo renaming (CANON.lean + OTD.lean, frozen atoms allowed): **if the phase-2 handler has a
  single wrapper (V = w.y; 836 of 1,083 real cases <= 11 leaves), then D3 = w[p:=c].p' is single-level, so every
  proper phase-3 transfer (if any) has a p'-headed innermost wrapper and phase 4 can never transfer (FH).**  So a
  Church chain through a single-wrapper handler has at most one more transfer phase.
* EXPERIMENTALLY SUPPORTED (goodhits2.py 21 400000 15 0.2; 72,652 random GOOD single-level phase-3 shapes W.p'):
  proper position-3 transfers occur ONLY when W is a c-comb (W = w[p:=c] with w a right comb over p with closed
  wrappers): 11 of 21,702 combs, 0 of 50,950 non-combs (LP with 2-3 C-args, SLP with 1-3 C-args).
* EXPERIMENTALLY SUPPORTED — THE REPLAY RELATION (replay2.py 11, p3trace2.py 11).  For a single-wrapper handler
  V = w.y, phase 3 is (by pure renaming) the generic run of w.q with q = p' live and p = c frozen.  Let
  theta = (replace every occurrence of w by p', then p by c).  If the phase-2 run passes through the list
  args(w) ++ [w, y, x.y, r] (38 of 836 single-wrapper cases <= 11 leaves), then phase 3 is EXACTLY the theta-image
  of phase 2 from that point (each step commutes with theta while no front is w-prefixed and no step re-creates w),
  so phase 2's transfer (p-front) is replayed as a REEXEC (c-front) of phase 3: observed in all 38 cases.  The
  same duality explains the c-comb counterexamples: with W = S(S(A.c)), phase 3 runs [A.c, y, p'.y] ->
  args(A) ++ [c, p'.y, y.(p'.y)], and phase 2 with w = S(S(A.p)) runs [A.p, S.L, y] -> args(A) ++ [p, y, (S.L).y]
  (here the map is p -> c, y -> p'.y); the same A-dynamics brings p (phase 2: TRANSFER) or c (phase 3: REEXEC) to
  the front first, or the other element first (phase 2: no transfer with this w; phase 3: the counterexample's
  p'-front).  So 'phase 2 transfers with w' and 'phase 3 transfers' are mutually exclusive along a replay.
  OPEN: a replay relation covering ALL real phase-2 outputs (the exact theta-alignment covers 38/836; other cases
  align only on the top part of the lists, with input maps such as y -> p'.y); this is exactly what a proof of
  'phase 3 is never proper' needs.
* MACHINE-CHECKED (agent_work/lean/YD.lean, 270 lines, Lean 4.35 core, no sorry; axioms propext, Quot.sound):
  Lemma YD.  `yd_main`: from any list satisfying YDI (no element is the bare y; no S-headed subterm has the bare y
  as a spine argument; every subterm d.y has d = x), no reachable list contains a proper y-comb (d1.(...(dm.y)),
  m >= 1, wrappers free of x, y, r) as an element — so no proper transfer at position 2 or 3, ever.
  `yd_bareS`: for every datum S.U with U S-headed and free of y, the generic run of [S.U, x, y, r] never contains a
  proper y-comb (the second step glues the bare y onto x.y and YDI holds from then on).  Atoms other than x, y, r
  are arbitrary (live or frozen), so this applies in every phase.
* MACHINE-CHECKED (agent_work/lean/REPLAY.lean, 235 lines, Lean 4.35 core, no sorry; axioms propext,
  Quot.sound): the REPLAY RELATION.  th w q c = replace (outermost) occurrences of the term w by the atom q and the
  live atom p = var 0 by c.  `replay_step` / `replay_run`: a head step (and hence a run) commutes with th as long as
  no front is w-prefixed and no step glues b onto d with b.d = w.  `replay_reexec`: if w is S-headed and the generic
  run of args w ++ [w, y, x.y, r] (= the run of the self-application w.w) reaches a p-headed front (TRANSFER) under
  these guards, then the generic run of the next phase's datum w[p:=c].q reaches after one more step the th-image
  of that list, whose front is c-headed (REEXEC).  So whenever a phase-2 run passes through args w ++ [w, y, x.y, r]
  and then transfers (the 38 aligned cases <= 11 leaves; replay2.py also checks the guards implicitly, since the
  replay ran to the end in all 38), the next phase re-executes the frozen value instead of transferring.
* MACHINE-CHECKED (agent_work/lean/MSLS.lean, 1,280 lines, Lean 4.35 core, no sorry; axioms propext,
  Classical.choice, Quot.sound): **Theorem MSL, STRICT form** — the core proof is now done once for an arbitrary
  level structure (a predicate Lev with: every level is a P-term; a level d.l' has d closed and l' a level), and
  instantiated twice.  `msl_glue_strict` / `msl_main_strict`: for the datum K.l (K closed, l = d2.(...(dk.p)) with
  closed wrappers, frozen atoms allowed), every P-element glued onto a Y-element is prefixed by one of the datum's
  OWN levels l, l', ..., p, or all of its P spine arguments are; hereditarily for all subterms w.q.  This is exactly
  the computationally certified classification of ml_wrappers.py (p-headed / level-prefixed / S-headed with only
  p-headed or level-prefixed P-arguments) and is strictly stronger than the generous form (`msl_glue_gen`, = MSL.lean),
  which also counts invented combs such as (S.S).L2 as levels.  The strict form matters: the general-shape phase-3
  counterexamples (goodhits*.py) all have generous-comb wrappers that are not datum levels.
* COMPUTATIONALLY CERTIFIED (target3.py 8 4 9 and 9 3 8; larger targeted families): (a) K <= 8 leaves x tails with
  wrappers <= 4 leaves (tail <= 9): 366,836 phase-2 runs, 13,041 proper position-3 transfers, phase 3: 9,371
  REEXEC, 3,212 non-proper p'-fronts, 458 calls, NO proper transfer; (b) K <= 9 leaves x tails with wrappers <= 3
  leaves (tail <= 8): 298,120 runs, 8,317 proper phase-2 transfers, phase 3: 7,318 REEXEC, 730 non-proper p'-fronts,
  269 calls, NO proper transfer.  Phase-2 data here have up to 18 leaves.
* PROVED (Creation lemma for the innermost wrapper; hand proof, general).  In a generic phase run, let the
  innermost wrapper vn of a proper handler be glued onto the bare y in the step [a, vn, y] ++ R0.  The element
  directly below vn is fixed from vn's creation until vn is at position <= 3; at position 3 a step [a1, a2, vn]
  inserts a2.vn directly below vn, after which y can never again be directly below vn.  The number of elements
  above vn changes by |args(front)| - 1 >= -1 per step and must be exactly 1 at the glue without ever being 2, so it
  is 1 from vn's creation on and the glue is the very next step.  Hence vn appeared one step before the glue with
  exactly one element above it: (alpha) created by [S, b0, c0, y] ++ R0 -> [c0, vn = b0.c0, y] ++ R0, or (beta)
  released as the second argument of an opened front with y directly below.  COMPUTATIONALLY CERTIFIED (wcreate.py
  11, all 836 single-wrapper real transfers): alpha 790 (b0 = S: 88), beta 46, nothing else.
* MACHINE-CHECKED (agent_work/lean/REPLAY.lean, now 300 lines; no sorry): `run_append` (the part of a list below
  the active top is never touched: run k T = some T' => run k (T ++ B) = some (T' ++ B)) and **`replay_glue`**:
  for a single wrapper w = S.c0 glued in pattern alpha, if the run of the top part [c0, w, y] reaches a p-headed
  front after k guarded steps (by run_append this is exactly the phase-2 TRANSFER above R0), then the phase-3 datum
  w[p:=c].q reaches after k+1 steps the th-image of that top part above [x.y, r], whose front is c-headed: REEXEC.
  COMPUTATIONALLY CERTIFIED (prefix_replay.py 11): for all 100 real single-wrapper transfers with w = S.c0
  (<= 11 leaves) the guards hold; 96 are pattern alpha and replay to a REEXEC exactly as the theorem says; 4 are
  pattern beta (not covered by replay_glue).
* PROVED (hand; single-level phase 3, i.e. single-wrapper phase-2 handler; P' = contains p', no x, y, r).
  Lemma Sigma2: if at some time the C-region has >= 2 elements while the P'-region is exactly [bare p'], then from
  then on either the C-region keeps >= 2 elements for ever (so no p'-front at all), or a BUFFER is created (a
  C-element glued onto the bare p').  [While |C| >= 2, p' sits at position >= 3, so the only step touching it glues
  the C-bottom onto it; by the MSL case analysis in the c-view, |C| leaves {2} downwards only by such a step, and
  |C| >= 3 is absorbing (Lemma AB with c as the live atom).]
  Lemma Gamma: if at some time the list is CL+ ++ [e] ++ [p'] ++ Y (one C-element e below >= 1 closed elements), then
  either |C| becomes 2 with P' = [p'] (a step [k1, k2, e] inserts k2.e) or a buffer is created ([k, e, p']), unless
  the phase ends first.  [The number of elements above e drops by at most 1 per step.]
  Consequence: for real single-wrapper handlers w = b0.c0 (pattern alpha) with b0 != S (702 of 836 cases <= 11
  leaves; plus the frozen-headed b0, which is FH), phase 3 starts in configuration Gamma (b0 closed) or with |C| >= 2
  (b0 a P-term), so 'phase 3 never makes a proper transfer' for this class REDUCES TO
  (B1) once a buffer has been created, no proper transfer follows (single-level phase 3).
  Together with replay_glue (b0 = S) only (B1) and pattern beta (46 cases <= 11) remain open for single-wrapper
  handlers.  Also (hand): before any buffer, a proper transfer's innermost wrapper vn (p'-headed by CANON) can only
  be glued onto y by a sigma_C step, after which the P'-region stays empty for ever (SL's 'hy': S-headed Y-elements
  release no P'-arguments), so the p'-front is a p'-headed Y-element.
