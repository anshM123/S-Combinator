# agent_work_U LOG (UNIVERSALITY agent, 2026-10-27)

Brief: construct a universal emulation by S alone (any evaluation order or multiway), with a non-universal
encoder/detector/decoder.  Labels: PROVED / MACHINE-CHECKED / COMPUTATIONALLY CERTIFIED / EXPERIMENTALLY SUPPORTED /
CONJECTURAL / REFUTED.  Deadlines (coordinator): INTERIM summary 04:00 EDT, refresh ~every 2 h, FINAL summary by 15:30 EDT.
All files of this agent live in agent_work_U/.

## 01:15 EDT start
* Read: PROOF.md (prize target, Theorem SI, U/U*, pump, write-pass, OT/OTD/SL, full re-execution frontier, bridge UB),
  agent_work/LOG.md, NEXT_STEPS.md head.  Tools: code/hc.py, code/symb.py, agent_work/hm.py.

## INTERIM 04:00 (refreshed 03:45 EDT; first version written 02:40)
**Status: no universal construction; no partial win (no non-PUP run).  Labels as in the entries below.**
Main results (files in agent_work_U/):
1. NEW FRAMEWORK, the descent machine DM (dm.py): leftmost-outermost evaluation along the leftmost Boehm path = the
   head machine plus the erasure rule [c, d] -> ch(c) at every head normal form (PROVED, elementary).  The only place
   where leftmost-outermost evaluation erases; by Lemma P it embeds in the head run of t A B.  Its sibling, the
   right-spine machine RM (rm.py: continue with d after the left child normalises), keeps everything (no erasure).
2. DM capabilities (PROVED by inspection): Church booleans in tail position (S X Y => X, SS X Y => Y), application
   (S(SS) X Y => X Y), identity SSSS, the selection gadget S(SS)(SS) E b => b (E b) (E (SS E) b): data-dependent
   SELECTION with the full state in both branches — the step the head-run capability map lacked.
3. DM limits — two MACHINE-CHECKED lemmas (Lean 4, no sorry):
   - W1 (lean/W1.lean, 160 lines): with one opaque datum D and closed code, every round's single-copy survivor is D or
     w.D (w closed): at most ONE closed wrap per round; hence copy-free single-datum leftmost paths only consume
     their stack (a finite automaton reading it), growth needs copies of the datum.
   - W2 (lean/W2.lean, 239 lines; reuses the main agent's Corollary 8(ii)): with two opaque data every round that
     ends has an atom-headed or closed survivor — no code-controlled state ever keeps two data across a round.
   Bounded certificates agree (survcat, twostack, twostack2, probe2, growth1; all negative).
4. Other orders: CBV/innermost (cbv.py) — nf(b x) is constant or fixed-prefix on string encodings (b <= 8), CBV
   iterations are exact linear recurrences (f <= 7); parallel clock channel — argued contractive (aging only
   pre-computes work; an hnf-free waiting element captures the head for ever); Prop. CF makes every head-fair order
   share the head run's control.  Remark (argued): W_reg with ARBITRARY regular redex selection is too generous —
   the order could act as a finite control using S-terms as memory; the target should be restricted.
5. Searches with negative outcome: word rounds, self-transforming words, comb halving, self-embedding Q ->* C[Q]
   (none <= 11 leaves), RM census (only Zachos-type long right spines <= 11 leaves).
Strongest concrete results: W1 and W2 (machine-checked), the DM selection mechanism.  No construction.
Next: multi-copy single-datum rounds (the only regime W1/W2 leave open) — classify survivors with >= 2 copies.

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
* NOTE (bug fixed 03:00): dm.truncate() did not clear the size cache; any size printed after truncate() in
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

## 02:45 EDT  The right-spine machine RM (rightmost Boehm path with finite left children)
* Observation (PROVED, elementary): if every left component normalises, leftmost-outermost evaluation finishes the
  left child c of each hnf S c d (emitting its normal form) and then evaluates d.  Along the right spine this is the
  list machine RM: head steps as usual; at [c, d] -> emit nf(c), continue with ch(d).  Since every round ends
  [S, b, c] -> [c, b.c], the next state is b.c: the element left at position 2 becomes the CODE and the bottom
  element c the DATUM; nothing is erased (the DM erases d, the RM keeps both).  After a write [SS, w, c] the next
  state is c.(w.c): the OLD datum is executed with the NEW datum as argument (data-dependent control for free).
  The emitted normal forms form an output stream (Boehm-level, so a universal RM would refute C5).

## 03:10 EDT  Lemma W1 (one closed wrap per DM round) — PROVED (elementary; agrees with survcat.py output)
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
* MACHINE-CHECKED (03:05 EDT): Lemma W1 in Lean 4 core — agent_work_U/lean/W1.lean (160 lines, no sorry; axioms
  propext, Classical.choice, Quot.sound; compile: ~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean W1.lean).
  `w1_survivor`: from C ++ [D] (C closed, D = var 0, atom-headed fronts stuck), every reachable 3-list [a, b, c] has
  0 < occ c, and occ c = 1 implies c = D or c = w.D with w closed.  Since a DM round ends exactly by [S, b, c] ->
  [c, b.c] with survivor c, this is the 'one closed wrap per round' lemma.  Invariant: phase 0 (closed prefix over the
  bare datum) or phase 1 (bottom and the element above it both contain D; a single-copy bottom is w.D, w closed).

## 03:25 EDT  Note on the prize target W_reg (arbitrary regular redex selection) — CONJECTURAL / argued
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

## 03:40 EDT  Lemma W2 — MACHINE-CHECKED (coordinator's suggestion)
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
* MACHINE-CHECKED (03:50 EDT): `w1_rm_next` added to agent_work_U/lean/W1.lean (still no sorry; axioms propext,
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
