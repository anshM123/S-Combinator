# agent_work_U LOG (UNIVERSALITY agent, 2026-10-27)

Brief: construct a universal emulation by S alone (any evaluation order or multiway), with a non-universal
encoder/detector/decoder.  Labels: PROVED / MACHINE-CHECKED / COMPUTATIONALLY CERTIFIED / EXPERIMENTALLY SUPPORTED /
CONJECTURAL / REFUTED.  Deadlines (coordinator): INTERIM summary 04:00 EDT, refresh ~every 2 h, FINAL summary by 15:30 EDT.
All files of this agent live in agent_work_U/.

## 01:14 EDT start
(Timestamps of later entries were corrected at 03:47 EDT on the coordinator's request: earlier labels ran ahead of
the clock; '~' marks times reconstructed from `date` outputs.  From now on every timestamp comes from `date`.)
* Read: PROOF.md (prize target, Theorem SI, U/U*, pump, write-pass, OT/OTD/SL, full re-execution frontier, bridge UB),
  agent_work/LOG.md, NEXT_STEPS.md head.  Tools: code/hc.py, code/symb.py, agent_work/hm.py.

## SUMMARY (refreshed 05:07 EDT by `date`; supersedes the INTERIM block below for the leftmost-path work)
**Universality: no construction (unchanged).  Since 04:03 working on the coordinator's suggestion: the leftmost-path
finite half for the joint classes (14,28), (14,26).  The finite half is NOT proved; new rigorous results below.**
1. MACHINE-CHECKED lean/TheoremV.lean (1,231 lines, no sorry): **Theorem V** — for closed W0 and a variable x, the
   leftmost walk of W0.x cannot go on forever while keeping x and never executing it (x-headed node or stuck round).
   Closed reading: an infinite leftmost path always consumes (executes) or drops its last argument — the precise
   form of 'the reload cycle N_i N_k S needs its fuel S'.  Ingredients: lean/Strip.lean (stripping theorem:
   `final_shape`, `no_R_chain`, `no_R2_chain`), lean/StripV.lean (k = 1 round lemma `k1_round`, `no_k1_walk`),
   W1+ (lean/W1F.lean), Lemma 8 / Cor. 8(ii) (main agent's BarrierJ.lean via lean/W2.lean).
2. PROVED (elementary): **large-push lemma** — with o(S) = 0, o(q.v) = omega^o(q) (+) o(v) (right-spine ordinal),
   every leftmost step decreases o except an 'o-large push' (a pushed multiplier q_i with o(q_i) >= o(q1)); an
   infinite leftmost path has infinitely many.  So the finite half <=> component walks have finitely many o-large
   pushes.  CERTIFIED census: <= 2 per walk (all component terms <= 10 leaves; 3,000 random 14-30 leaves), mostly
   peels (stack copies); the quadratic family t_k of Prop. S has exactly one size-large push for every k <= 9.
3. PROVED (elementary): **Scenario A** (bounded stack depth infinitely often) forces the multiplier above the frozen
   fuel to trace an infinite RIGHTMOST Böhm path (q -> snd H(q)); left open: Scenario B (unbounded stack, Omega
   type) and C (infinitely many jumps), and A itself needs the rightmost-path finite half (R19's open half).
4. Counterexample hunts (EXPERIMENTALLY SUPPORTED, none found beyond the 16-leaf census): reload-assembling trees
   (121,955 terms, <= 35 leaves), self-applications X X, X X S, S X X, X(SX), X S X for all X with 10-12 leaves,
   gadget-alphabet trees (<= 4 letters, 5 running), random component terms; every non-ending walk is in an L36
   flag-1 class.

## INTERIM 04:00 (refreshed 03:53 EDT by `date`; first version written ~02:38)
**Status: no universal construction; no partial win (no non-PUP run).  Labels as in the entries below.**
Main results (files in agent_work_U/; Lean files compile with ~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean):
1. NEW FRAMEWORK, the descent machine DM (dm.py): leftmost-outermost evaluation along the leftmost Boehm path = the
   head machine plus the erasure rule [c, d] -> ch(c) at every head normal form (PROVED; checked against genuine
   leftmost-outermost reduction, dmfaith.py).  Sibling: the right-spine machine RM (rm.py).
2. DM capabilities (PROVED): Church booleans in tail position (S X Y => X, SS X Y => Y), application S(SS), identity
   SSSS, selection gadget S(SS)(SS) E b => b (E b) (E (SS E) b).
3. COMPLETE CLASSIFICATION of fuel-free generic DM rounds — MACHINE-CHECKED (Lean 4 core, no sorry):
   - W1 (+W1-RM) lean/W1.lean; W1+ lean/W1F.lean: one datum => survivor closed, x, W.x or Fibonacci F_k(x, W.x);
   - W2 lean/W2.lean (uses main agent's Cor. 8(ii)); W2+ lean/W2F.lean: two data => survivor F_k(x, y);
   - comb rigidity lean/W2R.lean, lean/WR.lean: two data are carried across a round only by the empty code or a comb
     S^(j)(S); one datum: closed pre-computation, ONE write, then a comb;
   - corollary `shnf_two_vars` (WR.lean): M x y has an S-headed hnf only for M = S or M = S(comb j) (checked on
     all 82,500 terms <= 12 leaves);
   - >= 3 data: no round end (main agent's Cor. 8(i)).
   Caveat: 'fuel' (a closed element below the data, as in the reload cycle N_i N_k S) is outside these lemmas; the
   fuel catalogs show it only adds 'append the same fuel constant to the datum' (fuelcat*.py, bounded).
4. Other orders: CBV/innermost (nf(b x) constant or prefix-only, b <= 8; CBV iterations linear recurrences);
   parallel clock channel argued contractive; Prop. CF covers head-fair orders; W_reg with arbitrary regular
   selection would need a cell factory that S lacks in small sizes (no self-embedding term <= 11 leaves) — OPEN.
5. Negative searches: word rounds, self-transforming words, comb halving, periodic cells, RM long runs, two stacks.
Strongest concrete results: the machine-checked DM round classification and comb rigidity.  No construction.

## ~01:30 EDT  Direction chosen: the DESCENT MACHINE (leftmost-outermost along the leftmost Böhm path)
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
* COMPUTATIONALLY CERTIFIED (bounded, negative): survcat.py 8 2 3000 — for every closed C <= 8 leaves, the FIRST DM round
  of the state C x1 x2 (x1, x2 opaque) either executes a datum (atom-headed front) or ends with a survivor containing NO
  datum: with two opaque data the DM erasure can never keep data without re-executing data.  (With one datum the
  survivors are right combs c.x1 / S c1 c2 x1 and self-bundles like S x1 (x1 (S x1)): a pushdown with copy, i.e.
  higher-order-pushdown-like behaviour.)  combhalve3.py 6 2 14 4000: no q, v <= 6 leaves make the DM run of [D_n,q,v]
  reach a comb state [D_k, q', v'] at a round end with k - n non-constant on a parity class (no 'halving' gadget).
  selfword.py 3 5 4 4 600: no symbols A <= 3, B <= 5, E <= 4 make the head run of [S w E, x, y] carry a re-formatted word.
* PROVED (elementary, DM): (i) Church booleans in tail position: the state S X Y descends to X and SS X Y to Y
  (any X, Y): clean data-dependent SELECTION with both branches holding the full state.  E.g. G = S(SS)(SS):
  G E b => b (E b) (E (SS E) b) => E b (b = S) or E (SS E) b (b = SS).  (ii) A DM round that keeps data must end with
  the 3-list [S, b, c] (survivor c = the BOTTOM element); the bottom element only changes by wraps c -> w.c
  (w = the element above it), and each wrap leaves the old bottom as a stale copy above it, which only the final step
  [SS, w, D] -> [S, D, w.D] -> survivor w.D erases.  So with ONE datum the DM is a stack machine: per round pop (execute
  the top symbol: w = SS.J gives w.B => B), rewrite the top (S(SS)w'.B => w'.B) or push one closed symbol; a clean
  FIFO collector exists only for the symbol S (pump) — i.e. single-datum DM rounds are pushdown-like (selection =
  branching on the top symbol).  Two independent stacks would need a datum moved over another, which always leaves a
  stale bundle (A, B) -> (B, A.B).  Open: whether stale bundles can be made harmless (stale copies of the form SS.c
  act as 'drop c, keep next' = KI c in tail position).
* NOTE (bug fixed ~02:25 EDT): dm.truncate() did not clear the size cache; any size printed after truncate() in
  combcombs.py was unreliable (classifications end/budget were unaffected).  cbvsize.py: an apparent 'irregular' CBV
  size sequence was this artefact; after the fix, every CBV function nf(a u_n) with a <= 9 leaves (u_n = n nested S)
  has eventually affine size in n (n <= 14), and only a = S maps unary values to unary values (cbvfun.py 9 12).
* COMPUTATIONALLY CERTIFIED (bounded, negative): twostack.py 8 3000 6 — for all closed h <= 8 leaves and stack
  symbols a in {S(SS)S, S(SS)(SS), SSS, S(SSS)S}, the DM run of h.(a.X).Y (X, Y opaque stack rests) never reaches,
  within 6 round ends, a survivor C.P.Q (C closed) holding X once in P and Y once in Q other than the trivial
  'apply' survivor (a.X).Y.  No round modifies one stack while keeping the other (push/pop on either stack).
* COMPUTATIONALLY CERTIFIED (bounded, negative): cbviter.py 7 5 14 300000 — CBV iterations x_{k+1} = nf(f x_k) for
  normal forms f <= 7 leaves, x0 <= 5 leaves: every size sequence is an exact linear recurrence (ratios 3 or 4,
  e.g. f = SS(SSS): 1, 6, 21, 66, 201, ...); nothing irregular.  growth1.py 1 20000 5 6 4000 3: in 20,000 random
  single-datum DM runs (stack of 6 random symbols <= 5 leaves over an opaque base X) the comb depth over X never
  exceeds its initial value while X stays single — no stack growth without copying the datum, as predicted.
* Analysis (orders): by Proposition CF every head-fair order, and rightmost-outermost / innermost as long as the
  arguments normalise, follows the SAME Boehm-level control as the head run; they differ only in how far each piece of
  syntax has been evaluated (innermost: arguments in normal form).  So under innermost evaluation the syntax of a
  driver-built tower L_{m+1} = G[L_m] is the CBV iterate nf(G[L_m]) = BT(L_m).  A universal map x -> nf(G[x]) would
  therefore be Boehm-level universality (it would refute C5).  Being tested next: can nf(G[.]) act as a sequential
  transducer on string encodings enc(0w) = S enc(w), enc(1w) = S P enc(w)?
* COMPUTATIONALLY CERTIFIED (bounded, negative): cbvtrans.py 8 4 200000 (+ cbvtrans_filter.py; output
  agent_work_U/cbvtrans_8.txt) — for every normal form b <= 8 leaves and four (P, E) choices, the CBV normal forms
  nf(b enc(w)) (enc(0w) = S enc(w), enc(1w) = S P enc(w), |w| <= 4) contain an encoded string at a fixed address only
  as a constant (713 cases) or as u.w for a fixed prefix u (186 cases); one artefact (address hit depends on the first
  bit).  No internal rewriting: x -> nf(b x) is 'prefix-only' in this range (non-erasure duplicates x at every
  distributive step (S p q)*w = (p*w)*(q*w)).

## ~02:42 EDT  The right-spine machine RM (rightmost Boehm path with finite left children)
* Observation (PROVED, elementary): if every left component normalises, leftmost-outermost evaluation finishes the
  left child c of each hnf S c d (emitting its normal form) and then evaluates d.  Along the right spine this is the
  list machine RM: head steps as usual; at [c, d] -> emit nf(c), continue with ch(d).  Since every round ends
  [S, b, c] -> [c, b.c], the next state is b.c: the element left at position 2 becomes the CODE and the bottom
  element c the DATUM; nothing is erased (the DM erases d, the RM keeps both).  After a write [SS, w, c] the next
  state is c.(w.c): the OLD datum is executed with the NEW datum as argument (data-dependent control for free).
  The emitted normal forms form an output stream (Boehm-level, so a universal RM would refute C5).

## ~02:55 EDT  Lemma W1 (one closed wrap per DM round) — PROVED (elementary; agrees with survcat.py output)
*Statement.* Let C be a list of closed terms and D an opaque datum (an atom).  Run the DM from C ++ [D] until its first
descent, assuming no D-headed front occurs.  Then the survivor contains D, and if it contains D exactly once it is D or
c.D with c CLOSED.  (A multi-symbol push c1.(c2.D) is impossible in one round; the only other survivors contain >= 2
copies of D.)
*Proof.* (1) D is the bottom element and the bottom changes only by a wrap [a, X, B] -> ch(a) ++ [B, X.B] (B = bottom at
position 3), so the bottom always contains D; a round ends by [S, b, c] -> [c, b.c] with c the bottom (list length 3),
or by reaching a 2-list [U, bottom] whose first element U is the element directly above the bottom; the survivor is
the bottom or that U.  (2) Let U be the element directly above the bottom.  After the first wrap, U is the copy of the
old bottom, so U contains D.  U changes only when it is at position 3 (it is copied up and b.U, containing D, takes
its place), at position 2 (U absorbs the bottom; the bottom's copy, containing D, takes its place) or at position 1
(the round ends).  Elements created by a step land at positions <= |ch(a)|+2 above the touched elements and never
between U and the bottom.  So U contains D from the first wrap on, and every later wrap of the bottom uses a
D-containing wrapper: a second wrap gives >= 2 copies of D.  (3) Likewise U itself can receive at most one closed
wrap: after [a, b, U, bottom] -> ch(a) ++ [U, b.U, bottom] the copy of U sits directly above b.U, so the next
change of the element above the bottom uses a D-containing wrapper.  Hence a single-copy survivor is D, c.D or c.D'
with D' = D, c closed.  ∎
*Consequence.* With one datum and no copies the DM is a pushdown process with at most one push/pop/top-rewrite per
round (the 'controller' is the top symbol), i.e. a deterministic pushdown automaton; anything beyond needs copies of
the datum (higher-order-pushdown-like) or a second datum (which, by survcat.py, forces data execution).
* Corollary of W1 (PROVED): in the copy-free single-datum DM the closed-wrap depth over the base never increases
  (each round consumes the top symbol — executing the datum — or replaces the controller by one closed symbol), so
  a copy-free single-datum leftmost Boehm path is a finite automaton reading its stack top-down.  Growth needs a
  second copy of the datum (re-execution / order-2 behaviour, e.g. the Zachos copy-and-count-down round).
* COMPUTATIONALLY CERTIFIED (bounded, negative): probe2.py 11 3000 — no closed sigma <= 11 leaves turns sigma.x into
  x (c1 x) (c2 x) with exactly two arguments (two independent closed continuations each holding x once); 248 shapes
  exist only with >= 3 arguments, where the selectors S / SS no longer select.  So the leftmost path cannot branch on
  the top symbol while keeping the controller in BOTH branches in this range; the available probe x (c x) keeps the
  controller only in the 'select second' branch (S(S(SS))c . D => D (c D) => c.D if top(D) = SS, D_rest if top(D) = S).
  twostack2.py 7 30000 5 6 3 3000: 30,000 random two-stack configurations (symbols <= 5, controllers <= 6 leaves,
  stack depth <= 3): every survivor with both clean stacks is a pop of the active stack; no push, no change of the
  passive stack (15 changed cases, all pops).
* MACHINE-CHECKED (~03:00 EDT): Lemma W1 in Lean 4 core — agent_work_U/lean/W1.lean (160 lines, no sorry; axioms
  propext, Classical.choice, Quot.sound; compile: ~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean W1.lean).
  `w1_survivor`: from C ++ [D] (C closed, D = var 0, atom-headed fronts stuck), every reachable 3-list [a, b, c] has
  0 < occ c, and occ c = 1 implies c = D or c = w.D with w closed.  Since a DM round ends exactly by [S, b, c] ->
  [c, b.c] with survivor c, this is the 'one closed wrap per round' lemma.  Invariant: phase 0 (closed prefix over the
  bare datum) or phase 1 (bottom and the element above it both contain D; a single-copy bottom is w.D, w closed).

## ~03:05 EDT  Note on the prize target W_reg (arbitrary regular redex selection) — CONJECTURAL / argued
* PROOF.md's working target W_reg allows ANY regular redex-selection rule sigma.  By Proposition CF, an order that keeps
  contracting the head redex (with terminating excursions into arguments) follows the head run's Boehm-level control
  flow; the only other thing a regular sigma can do is (a) pre-evaluate arguments (finite excursions: changes syntax
  and timing only) or (b) commit to a descent into an argument (a walk on Boehm-tree paths, DM/RM type).  BUT a
  regular sigma may also choose WHERE to fire based on markers and bounded patterns, i.e. act as the finite control of
  a Turing machine that uses the S-term only as writable memory (fire a redex at the marked cell = write/move).  If
  S-rewrites suffice as such memory (plausible: firing at a marked position is a local, non-erasing write), W_reg is
  satisfied for reasons that have nothing to do with S computing ('hidden computation' in the order), and the same
  would hold for almost any growing rewrite rule.  So W_reg should be restricted (e.g. to head-fair orders, where
  Prop. CF reduces everything to the head run's control, plus explicitly descending/path orders such as DM and RM)
  before it is used as the disproof target.  Not constructed here: building it would not be accepted as S computing.
* EXPERIMENTALLY SUPPORTED: dmcensus.py 3 4000 18 30000 — of 4,000 random 18-leaf terms, 1,578 have a finite leftmost
  path (only 3 with >= 10 rounds) and 2,422 reach a node without hnf within < 10 rounds; none has >= 100 rounds in
  30,000 steps.  Long leftmost paths are rare (cf. LP1: infinite leftmost paths only in the D2 classes).
* W2 (two data force data execution) — status: COMPUTATIONALLY CERTIFIED for closed code <= 8 leaves (survcat.py);
  hand proof SKETCH: the bottom changes only at 3-lists [a, U, B]; U is never closed after the first wrap (the first
  wrapper of Y is X or X-derived, as in W1); a code-headed data element b.X in the data zone always has an
  atom-headed copy of X above it, which must be executed (stuck) or absorb downward (making an atom-headed element)
  before b.X can reach position 2 — so the last wrapper is atom-headed and every 2-data survivor is atom-headed.
  The invariant is of the same type as SL's INV-Q; NOT formalised.
* COMPUTATIONALLY CERTIFIED (bounded, negative): selfembed.py 11 400 — no closed Q <= 11 leaves (with a head redex)
  reaches, within 400 head steps, a term containing Q itself as a proper subterm (checked: all subterms of all list
  elements and the spine prefix S q1..qm).  No small 'self-reproducing' term Q ->* C[Q] exists along head reduction,
  so token factories for a regular-strategy 'S as RAM' design are not available off the shelf (increment would have to
  use duplication of a marked token).

## ~03:25 EDT  Lemma W2 — MACHINE-CHECKED (coordinator's suggestion)
* agent_work_U/lean/W2.lean (239 lines, Lean 4 core, no sorry; axioms propext, Classical.choice, Quot.sound).
  Framework and Corollary 8(ii) copied verbatim from the main agent's lean/BarrierJ.lean (attributed in the file);
  new: `dcount_two_atoms`, `dhead_start`, and
  - `w2_round`: a descent-machine round started from C ++ [x, y] (C closed, x, y atoms) that ends (reaches a list of
    length <= 2) ends with every data element atom-headed;
  - `w2_survivor`: the survivor c of a round ending at [c, d] is closed (all data erased) or atom-headed;
  - `w2_no_code_store`: no round ends with a code-headed survivor that still holds data.
  Reading: in the leftmost-path machine two opaque data can never both be kept under code control across a round;
  each round erases all data or hands control to a datum.  Together with W1 (one datum: at most one closed wrap per
  round) this closes the 'two independent stores' route for the DM at all sizes (generic/opaque data).
* EXPERIMENTALLY SUPPORTED (w2check.py 1 3000 4 7 200; w2check_out.txt): along 233,421 steps of random runs from
  C ++ [X, Y], the BOTTOM element is atom-headed at every step (0 violations) — stronger than W2, which only needs
  the hnf moment; the topmost data element and the middle of 3-lists can be code-headed transiently (1,348 / 495
  occurrences), so those stronger invariants are false.
* MACHINE-CHECKED (~03:32 EDT): `w1_rm_next` added to agent_work_U/lean/W1.lean (still no sorry; axioms propext,
  Classical.choice, Quot.sound).  For the right-spine machine (continue with the SECOND hnf component b.c after the
  left child normalises): the next state b.c holds D, and if it holds D exactly once then b is closed and c = D —
  a round of the right-spine machine either only replaces the closed controller or leaves >= 2 copies of the datum.
  (W2 needs no RM version: Corollary 8(ii) constrains every data element of the hnf list, so the RM's next state
  b.c is also closed or atom-headed whenever a round starts with two atom-headed data.)
* Correction to my own reasoning (02:55 note was not logged as a result): the converse of Lemma P is FALSE —
  SSS(SS)S(SS(SS)) = t A B with t = SSS(SS), whose leftmost path ends at the leaf S (t -> S(SS)(S(SS)) -> SS -> S),
  yet t A B has no hnf (Theorem BC).  So general infinite head runs are NOT just descent-machine runs plus inert junk:
  once t's leftmost path ends, the 'junk' arguments are executed.  W1/W2 constrain the DM/RM and every terminating
  hnf computation inside a head run, not hnf-free head runs as a whole.
* Analysis (argued, consistent with all certificates): why a DM/RM transducer (read a word, write a transformed word)
  is impossible for generic data: reading pops the executing datum (its rest is the first argument), the output must
  be a second datum, and W2 forbids any code-controlled state with two data across a round; the only way to 'write'
  the output while reading is the self-bundle x2 (c x2) (x1 x2), which hands control to the output and buries the
  remaining input as the third argument, beyond the order-3 window (BEKW Theorem 22 + barrier lemma).
* COMPUTATIONALLY CERTIFIED (faithfulness of the DM model): dmfaith.py — genuine leftmost-outermost reduction (one
  redex per step on the whole term) visits, in order, exactly the leftmost-path states predicted by dm.py:
  S(S(SS))(S(SS))(SS)S: all 740 DM survivors reached within 3,000 LO steps matched in order; S(S(SS))(S(SS))(S(SS)
  (S(S(SS))(S(SS)))): 1,473 matched.
* Refinement of the 03:25 W_reg note (now: OPEN, leaning 'not trivial for S'): an order-as-CPU construction needs
  (a) reusable cells — available in principle (e.g. a cell = an hnf-free subterm advanced by firing its head redex;
  its head-run list length mod p is a regular property), but no term <= 9 leaves has an eventually periodic top
  window (periodic_cell.py 9 3000, both with depth-2 shapes and with capped spine lengths), and (b) a FACTORY for new
  cells (an unbounded tape) — S has no small self-reproducing term (selfembed.py: none <= 11 leaves), duplication
  S x y z -> x z (y z) consumes its duplicator, so tape growth would have to come from an existing infinite run
  (e.g. the binary counter's growing list).  So whether W_reg is trivially satisfiable for S is itself non-trivial;
  not pursued further (an order-as-CPU emulation would not count as S computing anyway).

## ~03:36 EDT  Fibonacci classification of single-datum DM rounds (W1+)
* COMPUTATIONALLY CERTIFIED (copycat.py 11 4000): for every closed C <= 11 leaves, every survivor of the first DM
  round from ch(C) ++ [x] that holds x at least twice is a Fibonacci word F_k(x, W.x) — F_0 = x, F_1 = W.x,
  F_{k+2} = F_k F_{k+1}, W closed (here W = S c1 .. cj) — with k = 2..9 (2, 3, 5, ..., 34 copies; 29 shapes).
* Proof idea (to be machine-checked next): with x the only datum the list is (closed) ++ [x] until the first write
  [a, b, x] -> args a ++ [x, b.x]; from then on it is (closed) ++ [F_k, F_{k+1}] (W = b) — a step [a, F_k, F_{k+1}]
  gives args a ++ [F_{k+1}, F_k F_{k+1}] = (closed) ++ [F_{k+1}, F_{k+2}] — or a write [a, b, F_k, F_{k+1}] creates a
  third data element, after which (Lemma 8 + Corollary 8(i), main agent's BarrierJ.lean) no hnf is ever reached.
  So a round that ends has survivor closed, x, or F_k(x, W.x): the leftmost path's only copy mechanism is the
  Fibonacci swap of the comb, applied to (datum, one closed wrap of the datum).
* MACHINE-CHECKED (~03:38 EDT): agent_work_U/lean/W1F.lean (248 lines, Lean 4 core, no sorry; axioms propext,
  Quot.sound [+ Classical.choice for the survivor theorem]).  Framework/Lemma 8 copied from lean/BarrierJ.lean.
  `w1f_inv_reach`: every list reachable from C ++ [x] (C closed) is C' ++ [x] with C' closed, or
  C' ++ [fib W k, fib W (k+1)] with C', W closed, or has >= 3 data elements;
  `w1f_survivor`: the first element of every reachable 2-list (the DM survivor) is closed or fib W k, where
  fib W 0 = x, fib W 1 = W.x, fib W (k+2) = (fib W k)(fib W (k+1)).
  This is the complete classification of single-datum descent-machine rounds (it subsumes W1): the leftmost path can
  erase the datum, keep it, add ONE closed wrap, or copy it by the comb's Fibonacci swap of (x, W.x) — nothing else.
  (Agrees with copycat.py: all 29 multi-copy shapes <= 11 leaves are such Fibonacci words.)
* MACHINE-CHECKED (~03:40 EDT): agent_work_U/lean/W2F.lean (232 lines, Lean 4 core, no sorry; axioms propext,
  Quot.sound [+ Classical.choice for the survivor theorem]).  W2+ (sharpens W2): from C ++ [x, y] (C closed) every
  reachable list is C' ++ [fib2 k, fib2 (k+1)] (C' closed) or holds >= 3 data elements, where fib2 0 = x, fib2 1 = y,
  fib2 (k+2) = (fib2 k)(fib2 (k+1)); hence every DM survivor of a two-datum round is a Fibonacci word over (x, y)
  (`w2f_survivor`).  COMPUTATIONALLY CERTIFIED match (copycat2.py 10 3000): the data-holding survivors for closed
  C <= 10 leaves are exactly F_0..F_9 over (x, y), each produced only by the comb C = S^(k)(S).
* SUMMARY THEOREM (combining W1F, W2F and the main agent's Corollary 8(i)) — PROVED / MACHINE-CHECKED: a
  descent-machine round with closed code and opaque data ends (survives to the next leftmost-path node) only if it
  has <= 2 data elements, and then its survivor is
     1 datum x : closed, x, W.x, or a Fibonacci word F_k(x, W.x) (W closed);
     2 data x,y: a Fibonacci word F_k(x, y).
  The leftmost Boehm path therefore has exactly three generic operations on data — erase, ONE closed wrap, and the
  Fibonacci swap of the comb — between data executions.  A universal leftmost-path emulation would have to come
  entirely from what executed data do with Fibonacci-recombined arguments (each execution again satisfies the same
  classification for its own captured data), i.e. from re-execution — the regime the main agent conjectures to be
  call-like.
* Comb rigidity (PROVED by hand, ~03:42 EDT; Lean in progress): with two opaque data a closed prefix of length >= 2 can
  never shrink to length <= 1 without a step at length exactly 2, which is a write [p1, p2, F_k] (b = p2 closed,
  c = data) creating a third data element (then no hnf ever, Cor. 8(i)).  Hence a DM round from C ++ [x, y] ends
  without executing data iff C = [] or C = [S(S(...(S S)...))] (a comb S^(j)(S)), and then the survivor is F_j or
  F_(j+1) over (x, y).  For one datum the same holds after the first write: arbitrary closed pre-computation, ONE
  write by a closed W, then a comb.  The leftmost path's data-carrying code is literally the comb.
* MACHINE-CHECKED (~03:45 EDT): COMB RIGIDITY, agent_work_U/lean/W2R.lean (362 lines = W2F + 130 new lines; Lean 4
  core, no sorry; axioms propext, Classical.choice, Quot.sound).
  - `doomed_never_hnf`: from C ++ [fib2 k, fib2 (k+1)] with C closed and |C| >= 2 no list of length <= 2 is reachable;
  - `comb_rigid`: if a list of length <= 2 is reachable from [p, fib2 k, fib2 (k+1)] (p closed) then p = comb j,
    comb 0 = S, comb (j+1) = S.(comb j);
  - `w2r_rigidity`: a descent-machine round from C ++ [x, y] (C closed) can end only if C = [] or C = [comb j].
  The only closed code that carries two opaque data across a leftmost-path round is the comb S(S(..(S S)..)), whose
  effect is the Fibonacci swap (W2+).  (The one-datum analogue — arbitrary closed pre-computation, one write, then a
  comb — follows by the same argument; hand proof only.)

## ~03:46 EDT  Consequence: generic leftmost paths are countdown-and-reload processes (argued; rests on W1F/W2F/W2R)
* Sustained DM dynamics needs every round to end, so <= 2 data per round (Cor. 8(i)); by W2R the code of a two-datum
  round is a comb S^(j)(S) giving F_j(u, v); executing the survivor's head datum adds its rest to the data, so only
  j <= 3 can be followed by another ending round.  Reading the stack symbols as comb depths:
  - symbol S S (j = 1): survivor v — the head stack's rest is ERASED;
  - symbol S(SS) (j = 2): survivor u'v, then u' is executed with v passive: COUNT DOWN u with v passive;
  - symbol S(S(SS)) (j = 3): survivor v (u' v): v is executed with the bundle u'.v as partner — and popping that
    bundle later executes u' with the stale v plus the current partner: three data, no further round end.
  With one datum (W1F + the one-datum rigidity) the base of a countdown can write ONE closed W and copy by Fibonacci:
  e.g. survivor v (W v): count down v with partner W.v, then the same with W.v: the reload counter (Theorem C /
  reload cycles).  So for generic data the leftmost Boehm path is a countdown-and-reload process; data-dependence
  enters only through countdown lengths.  This (i) explains why Attempt U found only countdown/reload programs on
  leftmost walks, (ii) closes the leftmost path as a construction site, and (iii) suggests a proof route for the
  main agent's leftmost-path goals (a pushdown/HORS abstraction with states = comb depths and closed wraps W).
  Status: ARGUED from machine-checked lemmas; the multi-round composition is not formalised.
* MACHINE-CHECKED (03:47 EDT, `date`): agent_work_U/lean/WR.lean (280 lines, Lean 4 core, no sorry; axioms propext,
  Classical.choice, Quot.sound) — comb rigidity for an ARBITRARY pair of data u, v (Fibonacci family fibP u v):
  `rigid_pair`: if a list of length <= 2 is reachable from C ++ [u, v] (C closed, u, v data) then C = [] or
  C = [comb j]; `w1r`: one datum — after the first write [a, b, x] -> args a ++ [x, b.x] (a closed, b arbitrary) a
  round can end only if args a = [] or [comb j] (closed pre-computation, one write, then a comb); `w2r`: two data.
  (Note to the coordinator: timestamps in this LOG were corrected at 03:47 EDT; earlier labels had run ahead.)
* CORRECTION / CAVEAT (03:50 EDT, `date`): W1, W1+, W2, W2+ and WR are about F1 states (closed code ABOVE the data,
  nothing closed below them).  States with a closed element below the data ('fuel', PROOF.md's F1 violation) are not
  covered, and the reload cycle N_i N_k S uses exactly such fuel (the trailing S).  The 03:46 'countdown-and-reload'
  consequence therefore covers only fuel-free stretches; it is downgraded to ARGUED-WITH-GAP.
* COMPUTATIONALLY CERTIFIED (fuelcat.py 9 1 S 3000; fuelcat2.py 8 f 2000 for f = S, SS, S(SS), SSS): with one datum x
  and fuel f below it, the data-holding survivors of the first round are x, x.f (the datum re-absorbs the fuel
  UNCHANGED — 40 codes for f = S, only S(SS) for the other fuels), closed wraps W.(x.f), and Fibonacci words over
  (x.f, W.(x.f)) (15 shapes <= 9 leaves for f = S).  So fuel adds one operation — append the SAME closed constant
  f at the end of the datum's spine, which recreates the fuel for the next round (as in the reload cycle) — and
  otherwise the fuel-free classification applies to the datum x.f.  Fuel is never created by a fuel-free round
  (W1+: no fuel-free survivor ends with a closed spine argument after a datum), so it must come from the encoder.
* MACHINE-CHECKED (03:51 EDT, `date`): `shnf_two_vars` added to agent_work_U/lean/WR.lean (no sorry; axioms propext,
  Classical.choice, Quot.sound).  **For a closed S-term M, the head reduction of M x y (x, y variables) reaches an
  S-headed head normal form only if M = S or M = S(S(...(S S)...)) = S(comb j)**; conversely these give
  S F_j F_(j+1) over (x, y).  Every other M x y either becomes variable-headed or has no hnf.
  COMPUTATIONALLY CERTIFIED cross-check (shnf_check.py 12 2000): of all 82,500 closed terms <= 12 leaves exactly 12 have
  M x y reaching an S-headed hnf — S and S(comb j), j = 0..10 — and there is no counterexample.
* EXPERIMENTALLY SUPPORTED (dmlong.py 12 30000 300, 04:01 EDT): all 12-leaf terms whose leftmost path has >= 300 rounds
  (5 terms, 3 distinct profiles) are linear reload counters (round lengths 5/6 or 3/4; survivor sizes count down by 2
  or 3 and reload one step higher) — no nested (square) leftmost paths in this range, consistent with W2/W2R (no
  second independent counter on the leftmost path).

## Leftmost-path finite half for the component {(14,28),(14,26)} (coordinator suggestion 04:03) — started 04:04 EDT
* Tools (all in agent_work_U/): classes.py (joint L36 x M35 classifier over data/model36_leftpath.txt and
  data/model35_hn.txt, read-only), comp_runs.py / comp_detail.py / walkshow.py (leftmost walks with DM rounds),
  comp_shapes.py (809 distinct arg-class shapes of computed component nodes <= 10 leaves — the class abstraction of
  component nodes is very fragmented), reload_classes.py, reload_hunt.py, reload_hunt2.py, long_hunt.py.
* COMPUTATIONALLY CERTIFIED (04:28 EDT, reload_hunt2.py 5; output reload_hunt2_out.txt): over ALL trees with <= 5 letters
  from the alphabet {S, SS, B = S(SS)(SS), N1 = SS B, N2 = SS N1, S(SS)} (121,955 terms, up to 35 leaves, far beyond
  the 16-leaf census), every term whose leftmost walk reaches a reload node N_i N_k S (i >= 0, k >= 1; proved
  infinite, PROOF.md 'Reload cycles') within 80 nodes has an L36 flag-1 class (486 terms), and no other walk ran
  80 nodes without ending.  No inconsistency with L36.  (A first run used a loose pattern that also accepted
  N_i N_0 S; N_0 = B in the second slot does NOT reload — B is not of the form SS M' — so those 'hits' were false
  alarms; fixed before any conclusion was drawn.)
* EXPERIMENTALLY SUPPORTED: reload terms with other fuels, N_i N_k f for all closed f <= 8 leaves (i <= 2, k <= 3):
  classes (14,33) (no hnf) for 5,562 of them, (14,28) for 63, (9,28) only for f = S; e.g. N_1 N_3 (SS) walks into
  a node S(SS)(SS)(SS)(...) of class (14,33) whose round diverges.  The fuel must be exactly S: the round of
  [S, N, M, f] (M = SS M') reaches [f, M' f, N M f] and ends with survivor N M f only if args f = [] (f = S).
* Structural note (PROVED, elementary; = Lemma P/Lemma 7(iii) in the main agent's language): for u with >= 2 spine
  arguments, the head run of u.v follows u's leftmost path with a tail [v] that only grows (each 2-component node
  S x y maps the tail T to [T0, y T0] ++ T[1:], each 1-component node S x maps it to [T1, T0 T1] ++ T[2:]); hence
  u.v has an hnf only if u's path ends at the leaf S, and then u.v and the 'tau-node' S tau_0 ... tau_r (tau = tail
  when u's path reaches S) have the same leftmost child.  Consequences: u in P (infinite path) => u.v = bottom (this
  is L36's row 9 = all 14); P(u.v) <=> P(tau-node) when u's path ends at S.
* PROVED (elementary, 04:42 EDT `date`; agent_work_U/stackview.py, chainsrc.py, ordpush.py) — **multiplier-stack view and
  the large-push lemma.**  Write every node of the leftmost path through its right spine, u = q1 (q2 (... (qd S))), and put
  o(S) = 0, o(q.v) = omega^o(q) (+) o(v) (natural sum; o(u) < epsilon_0).  For u = q1.v: (i) q1 = S: child v (pop);
  (ii) q1 = S p: child p, a subterm of q1 (jump); (iii) q1 with >= 2 spine args: the child is
  c = q_{k-1}(...(q_0 v)) (Lemma 7(iii) / the Q10 tail chain: q_0 = second component of H(q1); a peel p = S x pushes
  the current stack, a refill pushes the second component of H(p w)).  So o(child) < o(u) unless (iii) pushes some q_i
  with o(q_i) >= o(q1) — an **o-large push**.  Since o is well-founded, **every infinite leftmost path has infinitely
  many o-large pushes** (same with sizes |q| and the Dershowitz–Manna multiset order: 'large pushes').  This replaces
  'new' steps (composite children) by a much rarer event as the thing a termination proof must control.
* COMPUTATIONALLY CERTIFIED (04:30–04:42 EDT, `date`): over ALL component terms <= 11 leaves (11,946; largepush.py 11) the
  number of size-large pushes per walk is 0 (11,528), 1 (377), 2 (38), 3 (3, all ending in bottom); over all component
  terms <= 10 leaves (3,377; ordpush.py 10) the number of o-large pushes is 0 (3,332), 1 (40), 2 (5); sources of
  o-large pushes: 67 peels (the pushed multiplier is a copy of the stack), 1 computed q_0.  The quadratic family t_k of
  Proposition S (path length k^2 + 3k + 3) has exactly ONE size-large push for every k = 0..9: its long paths are pure
  multiset descent.  The reload cycle has one large push per reload (source: computed q_0 = N_k (SS N_k)); the Omega
  walk S(S(SS))(S(SS))(S(S(SS))(S(SS))) has one per reload too (source: peel).
  => Reformulation (PROVED equivalent): the finite half for the component <=> component walks have finitely many
  o-large pushes.  EXPERIMENTALLY SUPPORTED: at most 2 (o) / 3 (size) per walk.
* EXPERIMENTALLY SUPPORTED (04:54 EDT, `date`; selfapp_hunt.py, selfapp_out.txt; rand_ord.py, rand_ord_1.txt; long_hunt2.py,
  long_hunt2_4.txt): no counterexample to the finite half beyond the 16-leaf census.  (i) Self-applications X X, X X S,
  S X X, X (S X), X S X for EVERY closed X with 10, 11, 12 leaves (5 x 76,444 terms, up to 25 leaves; leftmost walks
  <= 300 nodes): every walk that does not end within 300 nodes is in an L36 flag-1 class (14 terms, all Omega-type),
  and no flag-1 walk ends at S.  (ii) 3,000 random component terms with 14-30 leaves: at most 2 o-large pushes per
  walk, no walk longer than 300 nodes.  (iii) all trees of <= 4 letters over 8 gadget letters (S, SS, SSS, S(SS), B,
  M = S(S(SS))(S(SS)), SS(SS), S(SSS)): no flag-0 walk runs 400 nodes; at most 4 size-large pushes, and every walk
  with >= 3 of them ends in a diverging round.
* MACHINE-CHECKED (04:58 EDT, `date`): agent_work_U/lean/Strip.lean (402 lines, Lean 4 core, no sorry; axioms propext,
  Classical.choice, Quot.sound) — **stripping theorem** for closed S-terms.  `final_shape`: if L has >= 2 elements
  and the head run of L ++ [z] reaches a head normal form [c, d], then either c = z, the run of L alone reaches
  [S, y] and d = y.z (the bottom z was never wrapped), or c is strictly larger than z.  `no_R_chain`: there is no
  infinite sequence P0, P1, ... with H(P_j) = S S P_(j+1).  `no_R2_chain`: there is no infinite sequence
  W0, W1, ... with H(W_j) = S (S S) W_(j+1).  (Proof: such a chain strips its common last argument S resp. S S and
  becomes a chain of strictly smaller terms.)  COMPUTATIONALLY CERTIFIED cross-check (rchain_check.py 12): over all
  closed terms <= 12 leaves the R-chains have length <= floor((n-1)/2) and the stripping step holds in 2,983/2,983
  instances.
* PROVED (paper, from machine-checked parts; 04:58 EDT) — **Theorem V (opaque fuel cannot drive an infinite leftmost path).**
  Let W be closed and x a variable.  Along the leftmost walk of W.x, within finitely many nodes one of the following
  happens: the walk reaches the leaf S or a node without hnf, x is dropped (the node becomes closed), or x is
  executed (an x-headed node, or a round whose front is x-headed).  Proof: while x is kept, every node is W_j.x with
  W_j closed: by W1+ (lean/W1F.lean) a round from args(W_j) ++ [x] that ends has a closed survivor (x dropped) or a
  Fibonacci survivor fib W' k; k = 0 and even k give x-headed nodes; odd k >= 3 give a node whose list is
  args(W') ++ [x, F_2, F_4, ..., F_(k-1)] with >= 2 data, all x-headed, so by Corollary 8(ii) (lean/BarrierJ.lean,
  copied in lean/W2.lean) its round ends with a closed or x-headed survivor; nodes W_j.x with <= 1 argument in W_j
  give child x or a closed child.  So x is kept forever only through k = 1 rounds W_j.x -> W_(j+1).x, and a k = 1
  round forces H(W_j) = S (S S) W_(j+1) (the bottom is wrapped exactly once, by q = snd H(W_j); the remaining prefix
  args(p) ++ [x], p = fst H(W_j), must reach [S, b] without touching the bottom, which (bottom = x) is possible only
  in zero steps: args p = [S], p = S S).  no_R2_chain excludes an infinite such sequence.  [The k = 1 step is argued
  on paper; it is the atom analogue of final_shape and is not yet formalised.]  EXPERIMENTALLY SUPPORTED cross-check
  (opaque_walk.py 10): over all closed W <= 10 leaves, no walk of W.x keeps x unexecuted for 300 nodes.
  Meaning: the reload cycle's fuel S is essential — a leftmost-path computation driven by closed code above an
  untouched datum always halts, drops the datum or executes it (fuel must be consumed as S is in N_i N_k S).
* PROVED (elementary, 04:58 EDT) — **Scenario-A structure.**  If an infinite leftmost walk has bounded stack depth infinitely
  often (liminf of the right-spine depth d* < infinity), then from some node on the bottom part Z of the stack is
  frozen, no jumps occur, and at the return times (depth d*) the multiplier directly above Z follows
  q -> snd H(q): the chain from q.Z pushes q_0 = snd H(q) directly on Z, computed from q alone.  Hence **the
  multiplier above the frozen fuel traces an infinite RIGHTMOST Böhm path** (reload: N_i N_k -> N_(i-1) N_k -> ... ->
  B N_k -> N_k N_(k+1) -> ...).  So the leftmost finite half in Scenario A reduces to the rightmost-path finite half
  (R19's open half) plus the excursions; Scenario B (unbounded stack: the Omega walk) and Scenario C (infinitely
  many jumps) remain.
* MACHINE-CHECKED (05:03 EDT, `date`): agent_work_U/lean/StripV.lean (772 lines, Lean 4 core, no sorry, no warnings;
  axioms propext, Classical.choice, Quot.sound).  Namespace C = Strip.lean verbatim; namespace V = terms with
  variables and STUCK atom-headed fronts (W1F semantics), with the embedding emb of closed terms
  (`step_emb`, `reach_emb_inv`).  `V.k1_round`: if a closed list L (>= 2 elements) followed by a variable x reaches
  the hnf [w.x, d] with w closed, then L alone reaches [S S, w] (H(S L) = S (S S) w) — the k = 1 step of Theorem V,
  previously on paper.  `V.no_k1_walk`: there is no infinite sequence of closed W_j (>= 2 arguments) such that the
  head run of W_j.x reaches an hnf with first component W_(j+1).x.  Theorem V is now: machine-checked core
  (W1F + BarrierJ Cor. 8(ii) + StripV), with only the case split over the Fibonacci index k (k = 0, even k, odd
  k >= 3, short nodes) on paper (LOG entry 'Theorem V' above).
* MACHINE-CHECKED (05:07 EDT, `date`): **Theorem V, fully formalised** — agent_work_U/lean/TheoremV.lean (1,231 lines, Lean 4
  core, no sorry; `#print axioms V.theorem_V`: propext, Classical.choice, Quot.sound).  Statement `V.theorem_V`: for a
  closed S-term W0 and a variable x there is no infinite sequence u 0 = W0.x, u 1, u 2, ... with Child (u i) (u (i+1))
  for all i (Child: the first argument of a node with <= 2 arguments, or the first component of the head normal form
  reached by the head run of a node with >= 3 arguments, atom-headed fronts STUCK), every u i containing x and no u i
  headed by x.  The file contains Strip.lean (namespace C), the k = 1 round lemma, W1+ (copied from W1F.lean), the main
  agent's Lemma 8 / Corollary 8(ii) (copied from W2.lean / BarrierJ.lean) and the walk-level case analysis `v_step`
  (k = 0, even k, odd k >= 3 via Cor. 8(ii), short nodes).  Closed-term reading (substitution x := f, paper): along
  the leftmost path of a closed W0.f, within finitely many nodes the path ends, the occurrence f is dropped, or a
  residual of f is executed.  So an infinite leftmost path always consumes its last argument — as the reload cycle
  consumes the fuel S at every round.
* EXPERIMENTALLY SUPPORTED (05:08 EDT, `date`; long_hunt2.py 5 -> long_hunt2_5.txt; rand_ord.py 2 -> rand_ord_2.txt):
  (i) all 458,752 trees of exactly 5 gadget letters (S, SS, SSS, S(SS), B, M, SS(SS), S(SSS); up to 40 leaves):
  of the 248,370 flag-0 terms with an hnf, 173,960 walks end at S and 74,410 hit the round budget (probably bottom);
  NONE runs 400 nodes; size-large pushes per walk <= 4 (12 terms).  (ii) 6,000 random component terms with 25-60
  leaves: <= 2 o-large pushes per walk, no walk reaches 300 nodes.  No counterexample to the finite half.
* MACHINE-CHECKED (05:11 EDT, `date`): agent_work_U/lean/LargePush.lean (613 lines, Lean 4 core, no sorry; axioms propext,
  Classical.choice, Quot.sound) — **large-push lemma** (size version).  `LP.chain_ms` (Lemma 7(iii) in multiplier
  form): if q has >= 2 arguments and the head run of q.v reaches [c, d], then the right-spine multipliers of c are
  ps ++ (those of v) for some list ps (the child is q_(k-1)(...(q_0 v))).  `LP.large_push_lemma`: there is no infinite
  leftmost walk of closed S-terms in which no step is a large push (LargePush u c: u = q.v and some multiplier pushed
  on v is at least as large as q).  Measure: the stack of multiplier sizes in the multiset order (`LP.SStep`,
  well-founded by `LP.acc_all`).  So: **an infinite leftmost path has infinitely many large pushes**, and the finite
  half for any set of terms is equivalent to 'every walk from it has finitely many large pushes' (census: <= 3 per
  component walk up to 11 leaves, <= 4 over the 5-letter gadget trees).
* COMPUTATIONALLY CERTIFIED (05:14 EDT, `date`; lp_positions.py 11): in the leftmost walks of all component terms <= 11
  leaves, size-large pushes occur at computed-step index 0 (371), 1 (75), 2 (10), 3 (3), 4 (3) and nowhere later;
  consecutive large pushes are 1-3 computed steps apart; 453 of 462 happen at component nodes.  So in this range the
  walk spends its 'duplication capacity' at the start and then descends in the multiset order — unlike the reload
  cycle, which performs one large push per reload forever.

## 05:15 EDT — Finite-half report (self-contained, for the main agent)
Target (coordinator 04:03): every term in the joint classes (14,28), (14,26) has a finite leftmost Böhm path.
**Status: NOT proved.  No counterexample found.  Four rigorous structural results that any proof can use:**
(a) MACHINE-CHECKED lean/LargePush.lean — large-push lemma: infinite leftmost path => infinitely many large pushes
    (a computed step from q.v whose pushed multipliers include one at least as large as q).  Equivalently the finite
    half for a set of terms <=> finitely many large pushes along each of their walks.  The main agent's obstacle
    ('new' steps mix decreasing and growing slots) disappears for every step except large pushes, which are rare:
    census <= 3 per component walk (<= 11 leaves), all within the first 5 computed steps; ordinal refinement
    o(q.v) = omega^o(q) (+) o(v): <= 2 o-large pushes, mostly peels (stack copies).
(b) MACHINE-CHECKED lean/TheoremV.lean — Theorem V: closed code above an untouched datum cannot drive an infinite
    leftmost path (the last argument must be executed or dropped); the reload cycle executes its fuel S every round.
(c) MACHINE-CHECKED lean/Strip.lean — stripping theorem (no infinite H(P_j) = S S P_(j+1) or
    H(W_j) = S (S S) W_(j+1)); also: a fuel-S TAIL-CALL walk q_j.S -> q_(j+1).S (one push per step) is exactly a
    sequence with H(q_j) = S p_j q_(j+1) and (p_j = S S or H(p_j) = S S y) — the reload cycle is one; whether such
    sequences can start in the component is the class-dependent core of Scenario A.
(d) PROVED (elementary) — Scenario A (bounded stack depth infinitely often) => the multiplier above the frozen fuel
    traces an infinite rightmost Böhm path (q -> snd H(q)).
Remaining for a proof: control large pushes from component nodes (Scenario A via a rightmost-path argument;
Scenario B = unbounded stack, Omega-type self-application via peels; Scenario C = infinitely many jumps).
Evidence files: reload_hunt2_out.txt, long_hunt2_4.txt, long_hunt2_5.txt, selfapp_out.txt, rand_ord_1.txt,
rand_ord_2.txt; scripts in agent_work_U/*.py (classes.py, chainsrc.py, ordpush.py, largepush.py, lp_positions.py).
