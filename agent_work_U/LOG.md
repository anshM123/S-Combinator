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

## FINAL SUMMARY (refreshed 09:05 EDT by `date`; first written 06:54; earlier refreshes 07:31, 08:53)
**Brief (universality): no universal construction was found; no partial win.**  All results are obstructions or
structure theory, labelled below.  Nothing was submitted, posted or published.
**Coordinator task 04:03 (leftmost-path finite half for the joint classes (14,28), (14,26)): NOT fully proved; no
counterexample.  Since 07:31 the gap has been narrowed by machine-checked theorems: the finite half (for every L36
flag-0 class) now follows from ONE conjecture, EM: every infinite leftmost walk is eventually monotone (only
finitely many pops, jumps and returns, a return being a computed step whose child is the node's last argument).
Moreover one of EM's failure modes is now excluded outright (Scenario A over a non-tower fuel, no flag needed).**
MACHINE-CHECKED (Lean 4 core, no Mathlib, no sorry, axioms among propext / Classical.choice / Quot.sound; compile with
~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean <file>):
* agent_work_U/lean/FiniteHalfGen.lean (4,905 lines, ~1.5 min; = FiniteHalf.lean + namespaces FG, RG, FM, RM, SA;
  contains the main agent's lean/PathModels.lean verbatim as namespace PM):
  - FM.finite_half_monotone_all (NEW, strongest): no infinite leftmost walk from an L36-flag-0 term is eventually
    monotone, i.e. there are no j0, t, s with u (j0+j) = (t j).(s j), t j with >= 2 arguments, u (j0+j+1) /= s j.
  - FM.fib_step (Lemma Fib, NEW): over a bottom z that is not a tower S(S(...(SS))), every computed step is a
    Fibonacci step: H(Q) = S (tw K) c0 and the leftmost child is Fw K (Fw 0 = z, Fw 1 = c0.z, Fw (i+2) = Fw i . Fw (i+1));
    RM.fib_step2: the rightmost child is Fw (K+1).
  - SA.no_TT_chain (NEW): no infinite chain with H(W_j) = S (tw K_j) W_(j+1) (generalises no_R_chain, no_R2_chain).
  - SA.no_scenarioA (NEW, no flag): no jump-free infinite leftmost walk keeps a non-tower Z as a proper spine suffix of
    every node while returning infinitely often to nodes q.Z.  So in Scenario A the frozen fuel is a tower (half of
    Conjecture F).
  - FG.finite_half_Omega_general / FG.finite_half_general_families (NEW): no flag-0 walk ends in tail calls + Omega
    steps with ANY second component.
  - RG.finite_half_right_general, RM.finite_half_right_monotone_all (NEW, rightmost path / R19): no rightmost walk
    from an R19-flag-0 term eventually has only nodes with >= 3 arguments; R19's finite half reduces to EM_R.
  - unchanged from FiniteHalf.lean: FH.flag_step (L36 flag invariant along leftmost steps), FH.finite_half_TC,
    FH.finite_half_Omega, FH.finite_half_families, RR.flagR_step, RR.finite_half_right.
* agent_work_U/lean/FiniteHalf.lean (3,153), Reload.lean (1,587: reload classification), TheoremV.lean (1,416),
  LargePush.lean (613), Strip.lean (402), StripV.lean (772), and the earlier W1, W1F, W2, W2F, W2R, WR files.
COMPUTATIONALLY CERTIFIED: flag invariance on 16,580 concrete steps; counters N_k / w_k from R- / R2-chains into B / M
(<= 12 leaves); reload / Omega node classes; censuses of large pushes and jumps.
EXPERIMENTALLY SUPPORTED: Lemma Fib on 12,957 random instances (fibcheck.py); SF (hence EM) on 2,051 infinite walks /
619,000 steps after burn-in (only tail calls and canonical Omega steps); no counterexample to the finite half in about
1.5 million leftmost walks of targeted terms beyond the 16-leaf census.
PROVED (paper, from the Lean theorems plus liminf bookkeeping): Scenario A (jump-free, depth returning infinitely often
to its eventual minimum) has a tower fuel; its return multipliers follow q -> snd H(q).
CONJECTURAL: EM (leftmost) and EM_R (rightmost); SF / SF_R (stronger); Conjectures F (fuel = S), G.  For flag-0
terms EM can now fail only through (a) Scenario A over a tower fuel S(S(...)), (b) unbounded depth with infinitely
many pops/returns, (c) infinitely many jumps.  The L36 x M35 classes give no shortcut: SCC nodes can sit over every
tower bottom (towercls check, 09:0x).
Strongest concrete result: lean/FiniteHalfGen.lean, FM.finite_half_monotone_all — end-to-end machine-checked: an
infinite leftmost walk from a flag-0 term (e.g. any term of (14,28), (14,26)) must pop, jump or return infinitely
often (and, by SA.no_scenarioA, cannot do so by returning to a fixed level over a non-tower fuel).  Most promising
next step: (a) Scenario A over tower fuels (the excursion analysis starts from Lemma Fib over W = c.Z, which is a
non-tower), then (b) and (c).

## SUMMARY (refreshed 06:53 EDT by `date`; draft of the FINAL summary — supersedes the INTERIM block below)
**A. Universality (the brief): no universal construction; no partial win.  Machine-checked obstructions only.**
**B. Leftmost-path finite half for (14,28), (14,26) (coordinator, 04:03): NOT fully proved, no counterexample; both
known infinite mechanisms are EXCLUDED from flag-0 classes by end-to-end machine-checked theorems.**  All Lean files:
Lean 4 core, no Mathlib, no sorry, axioms among propext / Classical.choice / Quot.sound,
~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean.
1. lean/FiniteHalf.lean (2,911 lines; includes the main agent's PathModels.lean verbatim as namespace PM):
   `FH.flag_step` (the L36 flag is invariant along every leftmost step); `FH.finite_half_TC` (no flag-0 walk ends in
   tail calls over a fixed bottom — the reload mechanism); `FH.finite_half_Omega` (no flag-0 walk ends in tail calls
   plus canonical Omega steps — the Omega mechanism); `FH.finite_half_families` (any mixture of the two).
2. lean/Reload.lean (1,587): reload classification — every infinite chain of fuel-S tail calls is eventually the
   reload cycle N_i N_m S (`RC2.reload_classification_full`); no infinite tail calls over a bottom /= S.
3. lean/TheoremV.lean (1,416): Theorem V, leftmost and rightmost — an infinite path consumes its last argument.
4. lean/LargePush.lean (613): an infinite leftmost path has infinitely many large pushes.
5. lean/Strip.lean (402), lean/StripV.lean (772): stripping theorem, k = 1 round lemma.
6. Earlier: lean/W1, W1F, W2, W2F, W2R, WR — descent-machine round classification, comb rigidity.
7. Remaining gap for the full finite half: **Conjecture SF** — every infinite leftmost walk eventually uses only tail
   calls and canonical Omega steps (EXPERIMENTALLY SUPPORTED: 2,051 known infinite walks, 619,000 steps after burn-in).  SF + FiniteHalf.lean => the finite half.
8. Evidence (EXPERIMENTALLY SUPPORTED, no counterexample beyond the 16-leaf census): reload-assembling trees, gadget
   trees (<= 5 letters; 6 letters over 5 gadgets running), all self-applications with X <= 12 leaves and 40,000
   random X <= 24, random component terms up to 60 leaves, non-S fuels, R19-guided Scenario-A searches, restart-shape
   and generalized-Omega searches, jump searches.

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
* EXPERIMENTALLY SUPPORTED (05:17 EDT, `date`; fuel_hunt.py 4): Scenario A with a fuel other than S.  For W over all trees of
  <= 4 gadget letters and the 9 fuels Z in {SS, SSS, S(SS), SS(SS), S(SSS), S(S(SS)), SS(SSS), S(SS)S, S(SS)(SS)}
  (44,169 terms W.Z with an hnf), no leftmost walk keeps Z frozen for 300 nodes: 13,201 walks pop below Z, 14,480
  jump away (81 of them from flag-1 terms), 16,488 reach a round over the step budget (probably bottom).  CONJECTURE F (new): in Scenario A the frozen fuel is the leaf S
  itself (as in the reload cycle).  With (d), Scenario A would then reduce to fuel-S tail-call/excursion walks
  q_r.S -> q_(r+1).S along an infinite rightmost path.
* PROVED (elementary, 05:17 EDT) — **TC-chains (fuel-S tail calls) alternate R-chain segments and wraps.**  A fuel-S tail call
  q.S -> q'.S means H(q) = S p q' with p = S S or H(p) = S S y.  If q = Q.z with >= 3 arguments and the run never wraps
  the last argument z (m = 0), then by final_shape H(Q) = S S y and q' = y.z with the SAME last argument z: such
  steps are R-steps on the prefixes, finitely many in a row by no_R_chain.  So an infinite TC-chain wraps its last
  argument infinitely often (the reload cycle: countdown N_i N_k -> N_(i-1) N_k is an R-chain on the prefix SS N_(i-1),
  the reload B N_k -> N_k (SS N_k) is the wrap).
* MACHINE-CHECKED (05:21 EDT, `date`): **Theorem V for the RIGHTMOST path** added to agent_work_U/lean/TheoremV.lean (now
  1,416 lines, no sorry; `V.theorem_V_right`: propext, Classical.choice, Quot.sound).  RChild: the last argument of a
  node with <= 2 arguments or the second component of the hnf of a node with >= 3 arguments.  Statement: for closed
  W0 and a variable x there is no infinite rightmost walk of W0.x in which no node is headed by x.  Proof: from W.x the
  rightmost child is B.x with H(W) = S S B (phase 0 of W1+: the bottom was never wrapped; `r_round`), or a Fibonacci
  word fib W' (k+2) (x-headed for even k; for odd k the next round has >= 2 x-headed data and Cor. 8(ii) makes the next
  second component x-headed); the B's form an R-chain, finite by no_R_chain.  Since a rightmost walk never drops its
  bottom, **every infinite rightmost path executes its last argument within finitely many nodes** (closed reading by
  substitution).  Relevance: Scenario A of the leftmost finite half reduces to infinite rightmost paths, and this is
  the rightmost analogue of the fuel lemma — a tool for R19's open finite half as well.
* EXPERIMENTALLY SUPPORTED (05:24 EDT, `date`; jumpcount.py): along every known infinite leftmost walk (reload terms, Omega,
  and all flag-1 self-applications X X, S X X with X <= 11 leaves whose walks run 400 nodes) there is at most one jump
  and at most one pop, both at the first node; afterwards every step is a computed (chain) step.  Two shapes only:
  stack depth exactly 1 (nodes q.S: Scenario A with fuel S, every step a tail call) or slowly growing depth (Omega:
  Scenario B, depth 24-32 over nodes 200-400).  CONJECTURE G: every infinite leftmost walk is eventually jump- and
  pop-free and is either a fuel-S tail-call chain (H(q_j) = S p_j q_(j+1), p_j = S S or H(p_j) = S S y) or of
  Omega type (unbounded stack fed by peels).
* MACHINE-CHECKED (05:29 EDT, `date`): agent_work_U/lean/Reload.lean (613 lines, Lean 4 core, no sorry;
  axioms propext, Classical.choice, Quot.sound) — **reload lemma and restart theorem** for fuel-S tail calls.
  A node q.S continues as q'.S with a single pushed multiplier iff H(q) = S p q' with p = S S or H(p) = S S y
  (`TC.TCStep`).  `TC.reload_lemma`: if q = Q.z has >= 3 arguments and z /= S, such a step is an R-step on the prefix
  (H(Q) = S S y, q' = y.z) or produces the RELOAD SHAPE q' = w.(S S w).  `TC.R_shrinks`: R-steps shrink (|y| < |Q|).
  `TC.restarts`: in an infinite chain of fuel-S tail calls whose terms never have last argument S, the reload shape
  w.(S S w) recurs infinitely often.  So every infinite tail-call leftmost path over the fuel S is, structurally, a
  reload cycle: countdowns of the prefix by R-steps, and restarts w.(S S w) (B N_k -> N_k (S S N_k) is the case
  w = N_k).  Cross-check (tc_classify.py): the reload walks consist of R-steps and B-steps only; component walks
  also show 'other' tail calls (last argument S, or multi-wrap restarts such as S(S(SS))S(SS) -> S(SS)(SS(S(SS))),
  which is the reload shape with w = S(SS)).
* MACHINE-CHECKED (05:40 EDT, `date`): **RELOAD CLASSIFICATION THEOREM** — agent_work_U/lean/Reload.lean (now 1,076 lines,
  Lean 4 core, no sorry; `#print axioms RC.reload_classification`: propext, Classical.choice, Quot.sound).
  `RC.reload_classification`: an infinite chain of fuel-S tail calls q_j.S -> q_(j+1).S of the leftmost path (TCStep:
  H(q_j) = S p q_(j+1) with p = S S or H(p) = S S y) whose terms never have last argument S is EVENTUALLY EXACTLY THE
  RELOAD CYCLE: from some index on every q_j is N_i N_m with i < m, N_0 = B = S(SS)(SS), N_(k+1) = S S N_k.
  Steps: `RC.restart_detail` (with z /= S, S S a restart happens only at the prefix Q = B and gives z.(S S z):
  computed hnfs are never B, and multiple wraps would need z in {S, S S}); `RC.Rchain_to_B` (R-chains into a term
  whose last argument is not S are syntactic, so a prefix counting down to B is a counter N_d); `RC.next_restart`
  (between two consecutive restarts the prefix runs N_d, ..., N_0 = B); `RC.closure` (the set {N_i N_m : i < m} is
  closed under tail calls, by explicit head reduction); `RC.reach_det` (determinism).
  Meaning for the finite half: the only way a leftmost path can run forever by tail calls over the fuel S (depth-1
  Scenario A with no excursions), with last arguments avoiding S, is the reload cycle itself — whose terms the L36
  model puts in flag-1 classes (all reload-reaching terms checked: reload_hunt2.py).  What is left in Scenario A:
  tail-call chains that visit last argument S infinitely often, excursions above the fuel, Conjecture F (fuel = S);
  and Scenarios B (Omega type) and C.
* EXPERIMENTALLY SUPPORTED (05:40 EDT, `date`; selfapp_rand.py 7 40000 13 24 -> selfapp_rand_out.txt): 40,000 random X with
  13-24 leaves, terms X X, X X S, S X X, X (S X) (up to 50 leaves): every walk ends, hits the round budget, or (one
  term) runs 300 nodes in a flag-1 class.  No candidate counterexample.
* PROVED (from the machine-checked Theorem V by substitution; 05:41 EDT) — **fuel lemma for Scenario A.**  If an infinite
  leftmost walk returns infinitely often to nodes q.Z with a frozen bottom occurrence Z, then after every return a
  residual of that occurrence of Z is executed within finitely many nodes.  (At a return time treat the closed q as
  code and the bottom occurrence as the variable x; copies of Z inside q are not residuals of that occurrence and
  stay closed; the walks of q.Z and q.x coincide until a residual is executed; Theorem V forbids an infinite x-keeping
  walk, and in Scenario A the bottom is never dropped.)  For Z = S an execution is a pop (the reload cycle); for
  Z /= S it pushes args(Z) — Conjecture F says this cannot happen forever.
* OPEN (precise): fuel-S tail-call chains that pass through last argument S infinitely often.  Analysis so far
  (PROVED on paper): with last argument S, a tail call is an R-step on the prefix, a single wrap
  q' = b.(c S) with H(Q) = S x c and (x = S S, b = S — the chain then dies) or (H(x) = S S y, b = y S), or a multi-wrap
  restart w.(S S w) with w = c0.(S S); the chain returns to last argument S only through a 2-argument multiplier
  S a z (next multiplier z).  No size argument found for these periods yet.
* EXPERIMENTALLY SUPPORTED (05:42 EDT, `date`; scenA_hunt.py 12): Scenario-A hunt guided by the rightmost path.  In Scenario
  A the return multiplier has an infinite rightmost path; the R19 flag-1 terms (proved infinite rightmost path,
  Prop. Q'') with <= 12 leaves are only 18.  For each of them and the fuels Z in {S, SS, SSS, S(SS)}: with Z = S, 5
  walks run 300 nodes with Z frozen — all in L36 flag-1 classes (reload type) — and 10 end at S; with the other fuels
  every walk ends at S or reaches a diverging round.  Consistent with Conjecture F and with the reload
  classification; no counterexample.
* MACHINE-CHECKED (05:44 EDT, `date`): **Conjecture F, tail-call case** — added to agent_work_U/lean/Reload.lean (now 1,251
  lines, no sorry; axioms propext, Classical.choice, Quot.sound).  `FZ.tail_call_fuel`: if q has >= 2 arguments, Z is
  a closed term /= S, and the leftmost child of the node q.Z is q'.Z (one pushed multiplier: a tail call over the fuel
  Z), then H(q) = S (S S) q'.  `FZ.no_tail_calls_fuel`: there is NO infinite walk of tail calls q_j.Z -> q_(j+1).Z over
  a fuel Z /= S (it would be an infinite R2-chain, excluded by no_R2_chain).  Together with RC.reload_classification:
  **pure tail-call Scenario A is finite for every fuel other than S, and for the fuel S (last arguments avoiding S) it
  is exactly the reload cycle.**  What remains of Scenario A: excursions (returns after >= 2 pushed multipliers) and
  tail-call chains through last argument S.
* MACHINE-CHECKED (05:45 EDT, `date`): walk-level form added to agent_work_U/lean/Reload.lean (now 1,315 lines, no sorry; axioms propext, Classical.choice,
  Quot.sound).
  `FZ.tail_call_S`: if the leftmost child of the node q.S (q with >= 2 arguments) is q'.S, the multipliers make a
  fuel-S tail call (TCStep q q').  `FZ.walk_reload`: **an infinite leftmost walk through nodes q_j.S, each child being
  the next node q_(j+1).S (last arguments /= S), is eventually the reload cycle N_i N_m S.**  With
  FZ.no_tail_calls_fuel: an infinite leftmost walk that stays at depth one over a fixed fuel Z by tail calls exists
  only for Z = S, and is then the reload cycle (modulo last argument S).
* MACHINE-CHECKED re-run (05:47 EDT, `date`): all agent Lean files recompiled together — Strip (402 lines), StripV (772),
  TheoremV (1,416), LargePush (613), Reload (1,315), W1 (197), W1F (248), W2 (239), W2F (232), W2R (362), WR (293):
  no errors, no sorry, axioms only among propext / Classical.choice / Quot.sound.
* COMPUTATIONALLY CERTIFIED (05:48 EDT, `date`; flag_edges.py — a read-only re-implementation of code/leftpathcert.py's
  abstraction): **flag invariance along leftmost walks.**  Over the 69 joint classes and 39,049 tail-chain states of
  the main agent's chain graph G (Theorem Q10), no final chain state (s, b, beta) has a flag-0 node class
  kappa = s.s.b.beta (with hnf) and a flag-1 child class beta.  With the certified closure facts flag(s.x) = flag(x),
  flag(s.x.y) = flag(x) (Prop. Q'') and the soundness of G for computed steps (Theorem Q10's chain argument), every
  child of a flag-0 node with an hnf has a flag-0 class: **a leftmost walk that starts in a flag-0 class never visits
  a flag-1 node.**
* COMPUTATIONALLY CERTIFIED (05:48 EDT; reload_flags.py): the joint class of N_k is (27,13) for k = 0 and (31,12) for all
  k >= 1 (the sequence is constant from k = 1), and both class pairs give the reload nodes N_i N_m S (i < m) the
  flag-1 class (9,28).  So every reload node is flag 1.
* PROVED (from the machine-checked FZ.walk_reload / FZ.no_tail_calls_fuel and the two certified facts above; 05:48 EDT) —
  **first proved case of the finite half: Scenario A by tail calls.**  For a term in a flag-0 joint class (e.g. the
  component (14,28), (14,26)), the leftmost walk cannot end in an infinite tail of tail calls q_j.Z -> q_(j+1).Z over
  a fixed bottom Z, when Z /= S (no_tail_calls_fuel), or when Z = S and the multipliers' last arguments avoid S
  (walk_reload gives reload nodes, which are flag 1, while flag invariance keeps the walk in flag 0).
  Remaining cases of the finite half: Scenario A with excursions; depth-one tail calls through last argument S;
  Scenario B (unbounded stack, Omega type); Scenario C (infinitely many jumps).
* COMPUTATIONALLY CERTIFIED (05:52 EDT, `date`; jump_census.py 11): over all 23,714 closed terms <= 11 leaves, leftmost
  walks make at most 5 jumps (S(S(S(S(SSS)S)S)S)S: one per nested S(.)S layer), and every walk with a jump ends at S
  within 200 nodes; the 3 walks that run 200 nodes make no jump.  (Scenario C: no example.)
* PROVED (paper case analysis; 05:52 EDT) — **tail calls through last argument S or S S.**  Let q_j.S -> q_(j+1).S be fuel-S
  tail calls with last arguments z_j.  (1) R-steps keep z and shrink the prefix; a 2-argument multiplier S p z gives
  q' = z (so from z in {S, S S} the chain dies: S and S S have < 2 arguments).  (2) From z = S, a non-R step is either a
  multi-wrap restart w.(S S w) (then z' = S S w is not in {S, S S}), or a single wrap q' = b.(c S) with H(Q) = S x c and
  (x = S S, b = S: q' = S (c S) has one argument, the chain dies) or (H(x) = S S y, b = y S): then every later prefix
  keeps last argument S (R_strip), so it is never B (no restart) and never S p with p a fuel head (no 2-argument
  step); with c /= S the chain is a pure R-chain on the prefixes and dies (no_R_chain); with c = S (z' = S S) only a
  double-wrap restart can follow, giving z'' not in {S, S S}.  (3) From z = S S: single wrap only at prefix B, giving
  S S (S S (S S)), which dies; double wrap: restart.  (4) After a restart w.(S S w) the next non-R step is a restart at B
  (by restart_detail; two restarts give the reload cycle, RC.next_restart) or a 2-argument step S p (S S w) -> S S w,
  which dies.  Hence after the first multiplier with last argument in {S, S S} the chain dies or ends in the reload
  cycle, and **every infinite chain of fuel-S tail calls is eventually the reload cycle** (no hypothesis on last
  arguments).  With FZ.no_tail_calls_fuel and the certified flag facts: **no term in a flag-0 class has a leftmost
  walk that ends in an infinite tail of tail calls over a fixed bottom (Scenario A without excursions).**
  [Formalising (2)-(4) needs the z = S and z = S S variants of restart_detail; not done.]
* MACHINE-CHECKED (05:55 EDT, `date`): **full tail-call classification** — agent_work_U/lean/Reload.lean (now 1,587 lines,
  no sorry; axioms propext, Classical.choice, Quot.sound).  `RC2.tc_detail`: every fuel-S tail call from Q.z is an
  R-step, a restart w.(S S w), or (only for z = S) a single wrap S (c S) or (y S)(c S) with H(x) = S S y.
  `RC2.I_step` / `I_forever`: once the last argument has the form S S W it keeps it (2-argument steps from it die).
  `RC2.PS_step`: after a wrap from last argument S the prefix keeps last argument S and shrinks.
  `RC2.reload_classification_full`: **every infinite chain of fuel-S tail calls is eventually the reload cycle**
  (no hypothesis on last arguments); `walk_reload_full`: the walk-level form (nodes q_j.S, each child the next node).
  This supersedes the paper case analysis logged at 05:52 (now machine-checked).
  => **PROVED (machine-checked classification + the certified flag facts): no term in a flag-0 joint class — in
  particular no term in the component (14,28), (14,26) — has a leftmost walk that eventually consists of tail calls
  over a fixed bottom** (bottom /= S: FZ.no_tail_calls_fuel; bottom = S: the reload cycle, whose nodes are flag 1,
  unreachable by flag invariance).  Remaining for the finite half: Scenario A with excursions, Scenario B (unbounded
  stack; Omega type), Scenario C (infinitely many jumps).
* EXPERIMENTALLY SUPPORTED (05:57 EDT, `date`; scenA_gadget.py 5): q over all gadget trees of <= 5 letters with an R19 flag-1
  class (infinite rightmost path), fuel S: 228 walks run 400 nodes, all in L36 flag-1 classes; 19 of them make one
  excursion (a return to depth 1 after pushing two multipliers) and then only tail calls (reload).  Walks with
  excursions that end (at S or in a diverging round): 14.  No flag-0 walk runs 400 nodes.
* NOTE (05:57 EDT): over the fuel S, a step with H(q) = S (S(SS)) q' pushes q' and the fuel S, which is popped at once — an
  'Omega step' (the step of the Omega cycle, there over a growing stack).  RC2's TCStep excludes such steps; a
  classification of depth-1 walks mixing tail calls and Omega steps is the next case of Scenario A with excursions.
* PROVED + COMPUTATIONALLY CERTIFIED (05:58 EDT, `date`; flag_edges.py, flag_edges_check.py) — **flag invariance, simplified
  and validated.**  For a computed node u (>= 3 arguments) with head normal form S c (b c), class invariance of the
  S-models L36 and M35 under head reduction and the S-identity give [u] = s.[c].([b].[c]) = s.s.[b].[c].  So it suffices
  that for all b, beta in the 69-element sub-magma J generated by s: flag(s.s.b.beta) = 0 and s.s.b.beta in F imply
  flag(beta) = 0 — checked: no exception (flag_edges.py; no use of the chain graph G is needed).  Validation on
  concrete walks (flag_edges_check.py 11): all 16,580 computed steps of the leftmost walks of all terms <= 11 leaves
  are pairs ([u], [child]) of this form, and none goes from flag 0 to flag 1.
* MACHINE-CHECKED END-TO-END (06:09 EDT, `date`): **finite half of the leftmost-path model, tail-call scenario** —
  agent_work_U/lean/FiniteHalfTC.lean (2,487 lines, Lean 4 core, no sorry; `#print axioms FH.finite_half_TC`:
  propext, Classical.choice, Quot.sound; compiles in ~1.5 min).  Contents: namespace PM = the main agent's
  lean/PathModels.lean copied verbatim (L36/M35 tables, kernel-checked S-identities and closure facts, class
  invariance under head runs); namespaces C/TC/RC/FZ/RC2 = agent_work_U/lean/Reload.lean; namespace FH = bridge
  C.T -> PM.Tm, `FH.flag_step` (**the L36 flag is invariant along every leftmost step**, from the closure facts
  flag(s.x) = flag(x), flag(s.x.y) = flag(x) and class invariance — both directions; axioms propext, Quot.sound),
  `FH.flag_reload` (every reload node N_i N_m S, i < m, has flag 1: kernel computation of the classes of N_k), and
  `FH.finite_half_TC`: **an infinite leftmost walk from a closed S-term whose L36 class has flag 0 — e.g. any term
  of the joint classes (14,28), (14,26) — never ends in tail calls over a fixed bottom** (nodes (f j).Z for all
  j >= j0, each child the next node, f j with >= 2 arguments).  This makes the 05:55 'PROVED' statement fully
  machine-checked (the flag-invariance finite check of flag_edges.py is subsumed: flag(s.s.b.c) = flag(s.c.(b c))
  = flag(c) directly by the closure fact).
* EXPERIMENTALLY SUPPORTED (06:10 EDT, `date`; jump_gadget.py 5 -> jump_gadget_out.txt): Scenario C search over all 458,752
  gadget trees of <= 5 letters: every walk with >= 2 jumps ends (at S or in a diverging round) within 400 nodes; the
  650 walks that run 400 nodes make at most one jump, always at the first or second node (e.g. S S S (Omega-term) S).
  No walk with infinitely many jumps is known.
* SKETCH (ARGUED, not formalised; 06:12 EDT, `date`) — **the Omega cycle in the multiplier-stack view, and a roadmap for
  Scenario B.**  Write w_0 = M = S(S(SS))(S(SS)), w_(j+1) = S(SS) w_j.  The Omega walk visits exactly the nodes
  w_i . w_k (i < k): from w_i w_k (i >= 1) an R2-step (H(w_i) = S (SS) w_(i-1), a tail call over the bottom w_k),
  from w_0 w_k = M w_k an 'Omega step' (H(M) = S (S(SS)) (S(SS)): the chain pushes S(SS) and a COPY of the stack,
  child w_k (S(SS) w_k) = w_k w_(k+1)).  So Omega = the reload pattern with the fuel replaced by the second counter
  itself.  For a walk made only of R2-steps (q,Z) -> (q',Z), H(q) = S (SS) q', and Omega steps (q,Z) -> (Z, q'.Z),
  H(q) = S (S(SS)) q': R2-chains are finite (no_R2_chain), so Omega steps recur; with T_r the top after the r-th Omega
  step, T_(r+1) = q'_r . T_r; R2-chains into a term whose last argument is not S S are syntactic (the R_into argument
  for R2), so T_r = (S(SS))^n . Q*_r with an Omega base Q*_r = S (S(SS)) q'_(r+1); if q'_r = S(SS) from some r on,
  the base is constant and equals M, i.e. the walk is the Omega cycle.  The other branches (q'_r = S(S(SS)), computed
  bases, last arguments S S / S(SS)) are finite case analyses of the same kind as RC2.tc_detail.  Formalising this
  'Omega classification' (as Reload.lean did for the reload cycle) plus a proof that Scenario-B walks eventually use
  only R2/Omega steps would settle Scenario B via FH.flag_step (Omega nodes are flag 1).
* COMPUTATIONALLY CERTIFIED (06:17 EDT, `date`): (i) genomega_test.py 12 — the only closed X <= 12 leaves whose R2-chain
  (H(X) = S (SS) X1, H(X1) = S (SS) X2, ...) reaches a term with head normal form S (S(SS)) (S(SS)) are w_0 = M and
  w_1 = S(SS) M (as forced: a computed hnf S c (b c) is never S(S(SS))(S(SS)), and R2-steps into a term whose last
  argument is not S S are syntactic), and both M.X walks run 300 nodes in class (9,28).  (ii) the joint class of w_k
  is (8,21) for k = 0 and (22,26) for all k >= 1 (constant), and every Omega node w_i w_k (i < k) is flag 1.
  (iii) restart_hunt.py 7: all generalized restart shapes (w.(c.w)).Z with w, c <= 7 leaves and Z in {S, SS, S(SS),
  SSS}: no flag-0 walk runs 400 nodes (2 long walks, both flag 1).
  So, as for the reload cycle, the R2/Omega-step family pins down the canonical Omega cycle, whose nodes are flag 1;
  the missing piece for Scenario B is the analogue of RC2.tc_detail for Omega steps with second component /= S(SS).

## 06:18 EDT — Theorem map for the leftmost-path work (for the main agent; all Lean 4 core, no sorry)
| statement | Lean name | file | depends on |
|---|---|---|---|
| no infinite H(P_j) = S S P_(j+1) | C.no_R_chain | lean/Strip.lean | final_shape |
| no infinite H(W_j) = S (S S) W_(j+1) | C.no_R2_chain | lean/Strip.lean | no_R_chain |
| k = 1 round over a variable gives H(W) = S (S S) W' | V.k1_round | lean/StripV.lean | K1 invariant |
| Theorem V, leftmost (closed code over an untouched variable cannot run forever) | V.theorem_V | lean/TheoremV.lean | W1+, Cor 8(ii), no_R2_chain |
| Theorem V, rightmost | V.theorem_V_right | lean/TheoremV.lean | W1+, Cor 8(ii), no_R_chain |
| no infinite walk without large pushes | LP.large_push_lemma | lean/LargePush.lean | chain_ms, SStep well-founded |
| fuel-S tail call = R-step or restart w.(S S w) (last arg /= S) | TC.reload_lemma | lean/Reload.lean | final_shape |
| restarts recur in infinite fuel-S tail-call chains | TC.restarts | lean/Reload.lean | R_shrinks |
| eventually the reload cycle (last args /= S) | RC.reload_classification | lean/Reload.lean | restart_detail, Rchain_to_B, closure |
| tail calls over Z /= S force R2-steps; none infinite | FZ.tail_call_fuel, FZ.no_tail_calls_fuel | lean/Reload.lean | FInvZ |
| eventually the reload cycle (no hypothesis) | RC2.reload_classification_full, walk_reload_full | lean/Reload.lean | tc_detail, I_step, PS_step |
| L36 flag invariant along leftmost steps | FH.flag_step | lean/FiniteHalfTC.lean | main agent's PathModels (kCLft, clsLLft_run) |
| reload nodes are flag 1 | FH.flag_reload | lean/FiniteHalfTC.lean | kernel computation |
| **finite half, tail-call scenario** | **FH.finite_half_TC** | lean/FiniteHalfTC.lean | all of the above |
Paper-level (PROVED, elementary): Scenario A => infinite rightmost path of the return multiplier; fuel lemma for
Scenario A.  Certified: Omega nodes w_i w_k (i < k) are flag 1; only the canonical Omega family arises from R2-chains.
* CORRECTION / PRECISION (06:20 EDT, `date`): the 04:58 entry 'Scenario-A structure' derived 'no jumps occur' from bounded
  depth; that step is wrong in general — a jump (S p).Z -> p can land on a node p = f'.Z' whose bottom Z' is a COPY
  of Z (e.g. after a tail call whose second component is S (X Z)), keeping the depth.  The scenarios are therefore
  defined as: **A** = eventually jump-free and the stack depth is bounded infinitely often; **B** = eventually
  jump-free and the depth tends to infinity; **C** = infinitely many jumps (this now includes walks that mix tail
  calls with bottom-preserving jumps).  With this definition the Scenario-A statements stand (frozen bottom
  occurrence; return multipliers trace an infinite rightmost path; fuel lemma).  FH.finite_half_TC is stated for
  nodes (f j).Z with f j having >= 2 arguments, i.e. computed tail calls only — exactly the jump-free tail-call
  sub-case of A.  Walks that alternate tail calls and bottom-preserving jumps belong to C and are NOT covered.
* EXPERIMENTALLY SUPPORTED (06:21 EDT, `date`; stepfamily.py): along all 74 known infinite leftmost walks (flag-1 terms among
  the self-applications X X, S X X with X <= 11 leaves and the gadget trees <= 4 letters, walks of 400 nodes), after a
  burn-in of 50 nodes EVERY step is either a tail call (child q'.Z, one pushed multiplier, H(q) = S p q') — 24,946
  steps — or an Omega step (p = S(SS), child Z.(q'.Z)) — 954 steps; no pop, jump or other step occurs.
  **CONJECTURE SF (step families):** every infinite leftmost walk is eventually made of tail calls and Omega steps.
  Roadmap to the full finite half (each item checkable): (1) prove SF; (2) classify walks of tail calls + Omega
  steps (tail calls over S: DONE, RC2.reload_classification_full -> reload cycle; tail calls over Z /= S: R2-steps,
  finite in a row, FZ.no_tail_calls_fuel; mixtures with Omega steps: the canonical Omega cycle w_i w_k — sketch above,
  only canonical w_k arise, certified); (3) flags: FH.flag_step (machine-checked), reload nodes flag 1
  (machine-checked), Omega nodes flag 1 (certified, classes (8,21)/(22,26)).
* EXPERIMENTALLY SUPPORTED (06:22 EDT, `date`): all 954 Omega steps in the 74 known infinite walks (after burn-in) have
  second component q' = S(SS).  With q' = S(SS) at every Omega step the classification is short (paper proof):
  the stack after the r-th Omega step is S(SS).sigma_r, the next top sigma_r R2-counts down to the same base Y in
  every phase (R2-step S(SS).sigma -> sigma, then determinism), H(Y) = S(S(SS))(S(SS)) forces Y = M (a computed head
  normal form S c (b c) cannot have b c = S(SS) with c = S(SS)), and R2-steps into a term whose last argument is not
  S S are syntactic, so the first stack is some w_d and the walk is the canonical Omega cycle w_i w_k.

## 06:22 EDT — Paper proof of the reload classification (readable version of lean/Reload.lean, for audit)
Notation: closed S-terms; H(t) = head normal form, written as the 2-list [p, q'] for t with >= 2 arguments; a node
q.Z of the leftmost walk has top multiplier q and bottom Z.  A *fuel-S tail call* is a step q.S -> q'.S; it happens
iff H(q) = S p q' with p = S S or H(p) = S S y (FZ.tail_call_S; with p = S S the tail chain peels once, with
H(p) = S S y it refills once: H(p S) = S S (y S)).  R(P, P') means H(P) = S S P'.
(1) final_shape: if L has >= 2 elements and L ++ [z] reaches [c, d], then either no step ever touched the bottom z —
    then c = z, L reaches [S, y] and d = y.z — or c is bigger than z (the bottom only grows, by b.bottom).
(2) R-chains are finite (no_R_chain): for P with >= 3 arguments, R(P, P') forces P = Q.S, R(Q, y), P' = y.S by (1);
    so an infinite R-chain of P's yields one of the strictly smaller Q's; induction on size.  R-steps shrink.
(3) tc_detail: from q = Q.z (Q with >= 2 arguments) a tail call is an R-step on the prefix (H(Q) = S S y,
    q' = y.z), a restart q' = w.(S S w), or — only for z = S — a single wrap S (c S) / (y S)(c S).  Proof: track the
    last wrap [x, c, w] -> args x ++ [w, c w] of the bottom (invariant CInv with the wrap history); at the end the
    prefix args x ++ [w] reached [S, b]: for w /= S this forces x = S S and b = w by (1), and the tail-call condition
    on p = c.w forces c = S S.
(4) restart_detail: if z is neither S nor S S, a restart only happens with the prefix Q = B = S(SS)(SS) and gives
    q' = z.(S S z): the last wrap [S S, S S, w] came from a prefix reaching [S S, S S], which is never the result of
    a step ([c, b.c] = [S S, S S] is impossible), so it is the first wrap and w = z, args Q = [S S, S S].
(5) Rchain_to_B: an R-step into a term whose last argument is not S is syntactic (R(Y, V) => Y = S S V), so a prefix
    that counts down to B in t steps is N_t = (S S)^t B.
(6) Once the last argument has the form S S W it keeps it (I_step: R-steps keep it, restarts produce it,
    2-argument steps S p (S S W) -> S S W die); before that, the chain either shrinks (R-steps, 2-argument steps) or
    passes a wrap from last argument S, after which the prefix keeps last argument S and only R-steps remain (PS_step)
    — finitely many.  So the invariant is reached.  Then restarts recur (the chain cannot shrink forever), and between
    two consecutive restarts the prefix runs N_d, ..., N_0 = B by (4), (5); the set {N_i N_m : i < m} is closed under
    tail calls by direct head reduction.  Hence the chain is eventually the reload cycle.
(7) Finite half, tail-call case: the L36 flag is invariant along leftmost steps (closure facts flag(s x) = flag(x),
    flag(s x y) = flag(x) and class invariance under head reduction: [u] = [S c (b c)] for a computed node), and
    every reload node N_i N_m S is flag 1 (classes of N_k are constant for k >= 1).  A flag-0 walk can therefore not
    end in the reload cycle; over a bottom Z /= S tail calls are R2-steps, and R2-chains are finite by (2).
* MACHINE-CHECKED END-TO-END (06:38 EDT, `date`): **finite half, Omega scenario** — agent_work_U/lean/FiniteHalf.lean
  (2,859 lines; supersedes FiniteHalfTC.lean, which it contains; no sorry; axioms propext, Classical.choice,
  Quot.sound).  New: `OM.omega_detect` (if the leftmost child of t.sigma (sigma /= S, t with >= 2 arguments) is
  sigma.(q'.sigma), then H(t) = S (S(SS)) q'; proof by a full wrap-history invariant WH), `OM.Om_M` (H(Y) =
  S(S(SS))(S(SS)) forces Y = M), `OM.Rchain_to_M` (an R2-chain ending at M starts at a counter w_d),
  `FH.flag_omega` (all Omega nodes w_i w_k with i < k or i = 0 are flag 1, kernel computation), and
  `FH.finite_half_Omega`: **an infinite leftmost walk from a flag-0 term (e.g. in (14,28), (14,26)) never ends in
  nodes (t j).(s j) whose steps are tail calls over the stack (s (j+1) = s j) or canonical Omega steps
  (t (j+1) = s j, s (j+1) = S(SS).(s j)).**  So both known infinite mechanisms — the reload cycle and the Omega
  cycle — are excluded from flag-0 classes by machine-checked proofs.  Remaining for the full finite half: Conjecture SF
  (every infinite walk eventually uses only tail calls and Omega steps) and Omega steps whose second component is not
  S(SS) (never observed: all 954 Omega steps in known infinite walks have q' = S(SS)).
* MACHINE-CHECKED (06:53 EDT, `date`): `FH.finite_half_families` added to agent_work_U/lean/FiniteHalf.lean (now
  2911 lines, no sorry; axioms propext, Classical.choice, Quot.sound): **an infinite leftmost walk from a
  flag-0 term (e.g. any term of (14,28), (14,26)) never ends in a sequence of computed nodes (t j).(s j) whose steps
  are tail calls over the stack (s (j+1) = s j) or canonical Omega steps (t (j+1) = s j, s (j+1) = S(SS).(s j))** —
  any mixture of the two known infinite mechanisms (finitely many Omega steps: finite_half_TC; infinitely many: the
  stack is never S afterwards and finite_half_Omega applies).  (Process note: a stray 'cat' in my shell command
  blocked for 10 minutes; I stopped my own cat process, PID 76440, and the compile then completed.)
* EXPERIMENTALLY SUPPORTED (06:53 EDT, `date`; long_hunt3.py 6 -> long_hunt3_6.txt): all 656,250 trees of exactly 6 letters
  over {S, SS, S(SS), B, M} (up to 42 leaves): of the 385,663 flag-0 terms with an hnf, 266,054 walks end at S and
  119,609 reach a round over the step budget; none runs 400 nodes; size-large pushes per walk <= 4.  No candidate.
* EXPERIMENTALLY SUPPORTED (06:56 EDT, `date`; omega_general_hunt.py 7): walks started at non-canonical Omega bases
  (S(S(SS)) q').sigma for all q', sigma <= 7 leaves (38,809 terms with an hnf): every walk ends (at S: 21,903; in a
  diverging round: 16,905) except one, which runs 300 nodes in a flag-1 class using only canonical Omega steps;
  non-canonical Omega steps (second component /= S(SS)) occur at most 3 times per walk.  Supports SF's restriction to
  canonical Omega steps.
* EXPERIMENTALLY SUPPORTED (07:07 EDT, `date`; stepfamily2.py 5): all 211 flag-1 terms among the 5-letter gadget trees over
  {S, SS, S(SS), B, M} whose walks run 400 nodes: after a burn-in of 100 nodes every one of the 63,300 steps is a tail
  call (61,159) or a canonical Omega step (2,141); no pop, jump, non-canonical Omega step or other step.  (SF.)
* MACHINE-CHECKED END-TO-END (07:30 EDT, `date`): **rightmost path (R19), reload scenario** — added to
  agent_work_U/lean/FiniteHalf.lean (now 3,153 lines, no sorry; axioms propext, Classical.choice, Quot.sound).
  `RR.flagR_step`: the R19 flag is invariant along every rightmost step (closure facts flag(s x) = flag(x),
  flag(s x y) = flag(y) of the main agent's PathModels + class invariance).  `RR.right_tail_detect`: a rightmost
  child t'.sigma of t.sigma forces H(t) = S S t'.  `RR.right_reload_detect`: a rightmost child sigma.(S S sigma)
  (sigma /= S) forces t = B (single wrap of the bottom by S S, prefix [S S, S S]).  `RR.finite_half_right`: **a
  rightmost walk from a term whose R19 class has flag 0 never ends in computed nodes (t j).(s j) (s j /= S) whose
  steps are rightmost tail calls (s (j+1) = s j) or canonical rightmost reload steps (t (j+1) = s j,
  s (j+1) = S S (s j))** — the rightmost path of the reload cycle (N_i N_k -> N_(i-1) N_k -> ... -> B N_k ->
  N_k N_(k+1)), whose nodes all have R19 class 4 . 4 = flag 1 (`RR.flagR_N`, kernel computation).  This is the
  first proved case of R19's open finite half ((D2') for the rightmost path).
* EXPERIMENTALLY SUPPORTED (07:31 EDT, `date`; stepfamily_right.py): for the RIGHTMOST path, all 609 R19-flag-1 walks among
  the gadget trees (<= 5 letters over {S, SS, S(SS), B, M}) and the self-applications X X (X <= 10 leaves): after a
  burn-in of 60 nodes, every one of the 146,160 rightmost steps is a rightmost tail call (138,193) or a canonical
  rightmost reload step sigma.(S S sigma) (7,967).  **CONJECTURE SF_R:** every infinite rightmost walk eventually uses
  only these two step types.  SF_R + RR.finite_half_right => R19's finite half (=> (D2') for the rightmost path).

## 07:32 EDT — Paper proofs of the Omega and rightmost results (readable versions of lean/FiniteHalf.lean, for audit)
**Flag invariance (FH.flag_step, RR.flagR_step).**  L36 and M35, R19 are S-models, so the class of a term is
invariant under head reduction (main agent's clsLLft_run / clsLRgt_run).  For a computed node u with head normal
form S c (b c): [u] = s.[c].[b c]; the certified closure facts flag_L(s.x.y) = flag_L(x) and flag_R(s.x.y) = flag_R(y)
give flag_L(u) = flag_L(c) (c = leftmost child) and flag_R(u) = flag_R(b c) (b c = rightmost child); short nodes S x,
S x y are handled by flag(s.x) = flag(x) and the same two-argument facts.  Hence each flag is constant along its path.
**Omega detection (OM.omega_detect).**  Track the complete history of wraps of the bottom sigma during the head run of
t.sigma (inductive WH: each wrap [x, c, w] -> args x ++ [w, c w] records how its 3-list arose — from the run of t for the
first wrap, from the run of args x0 ++ [w0] for later ones).  If the leftmost child is sigma.(q'.sigma), the final
2-list is [c w, b (c w)] with c = sigma, w = q'.sigma, so the last wrap was preceded by a wrap of sigma by q'; its
prefix args x0 ++ [sigma] reached [S S, sigma], which (final_shape, sigma /= S) is only possible in zero steps:
x0 = S(SS); and that wrap was the first one (a later one would make sigma a wrap of itself): the run of t reached
[S(SS), q'], i.e. H(t) = S (S(SS)) q'.
**Omega classification (FH.finite_half_Omega).**  Tail calls over a stack /= S are R2-steps of the top (FZ.tail_call_fuel),
finitely many in a row (no_R2_chain), so canonical Omega steps recur.  At a canonical Omega step the top Y has
H(Y) = S (S(SS)) (S(SS)), forcing Y = M (a computed hnf S c (b c) never has b c = S(SS) with c = S(SS)).  Between two
consecutive Omega steps the tops form an R2-chain from the old stack down to M; R2-steps into a term whose last argument
is not S S are syntactic, so the old stack is a counter w_d.  From then on the states are (w_i, w_k) with i < k (or i = 0),
a set closed under both step types; all these nodes are flag 1 (classes (8,21), (22,26)), contradicting flag invariance.
**Rightmost reload (RR.finite_half_right).**  A rightmost child t'.sigma of t.sigma: by final_shape the bottom was never
wrapped and H(t) = S S t' (otherwise the first component is bigger than sigma, while the final step [S, b, c] ->
[c, b c] forces c = sigma).  A rightmost child sigma.(S S sigma): the bottom was wrapped once, by S S, at the first
wrap, whose prefix (the run of t) reached [S S, S S], i.e. t = B.  R-chains are finite, so reload steps recur; between
them the tops count down an R-chain from the old stack to B, which is syntactic (Rchain_to_B), so the old stack is N_d;
every node N_i N_k has R19 class 4.4 = flag 1, contradicting flag invariance.
* EXPERIMENTALLY SUPPORTED (07:39 EDT, `date`; stepfamily2.py 6): all 1,766 flag-1 terms among the 656,250 six-letter gadget
  trees over {S, SS, S(SS), B, M} whose walks run 400 nodes: after a burn-in of 100 nodes all 529,800 steps are tail
  calls (510,735) or canonical Omega steps (19,065).  SF evidence in total: 2,051 infinite walks, 619,000 steps, no
  exception.

## 07:55 EDT — MACHINE-CHECKED: Omega steps with ANY second component (lean/FiniteHalfGen.lean)
* agent_work_U/lean/FiniteHalfGen.lean (3,395 lines = lean/FiniteHalf.lean verbatim + namespace FG; Lean 4 core, no sorry;
  compiled by path with v4.35.0, exit 0, 0 errors; axioms of both new theorems: propext, Classical.choice, Quot.sound).
* FG.finite_half_Omega_general: an infinite leftmost walk from an L36-flag-0 term never ends in computed nodes
  (t j).(s j) (t j with >= 2 arguments, s j /= S) whose steps are tail calls over the stack (s (j+1) = s j) or Omega
  steps with ANY second component q (t (j+1) = s j, s (j+1) = q.(s j)).  FG.finite_half_general_families: the same with
  the bottom allowed to be S (so it also covers the reload mechanism and any mixture).  This removes the restriction
  'canonical (q = S(SS))' from FH.finite_half_Omega / FH.finite_half_families.
* Paper proof.  FG.top_tc / FG.top_om: if a top is q.sigma with size sigma >= 4, then a tail call from it forces
  q = S(SS), and an Omega step from it with second component p forces q = S(S(SS)) and p = sigma (if q has >= 2
  arguments, final_shape makes the first hnf component equal to sigma or larger than sigma, so it is not S S /
  S(SS); if q = S x, the hnf is S x sigma).  After an Omega step at j with second component q the stack is
  q.(s j) and stays so until the next Omega step j1, after which it is the TOP: t (j1+1) = q.(s j).  So q = S(SS)
  or q = S(S(SS)); in the latter case step j1+1 is itself an Omega step with second component s j, and at the next
  Omega step j3 the top is (s j).(s (j1+1)), so s j is S(SS) or S(S(SS)) (size <= 4).  Stack sizes grow at every
  Omega step and there are infinitely many Omega steps (no infinite R2-chain), so from some J on size (s j) >= 6 and
  every Omega step is canonical; FH.finite_half_Omega finishes.
* Consequence for the gap: Conjecture SF may be weakened to SF- : every infinite leftmost walk eventually consists of
  computed steps that push exactly one multiplier over the same bottom (tail calls) or push the old stack plus one
  multiplier (Omega-type, any second component).  SF- + FiniteHalfGen.lean => leftmost finite half for flag-0 classes.

## 08:02 EDT — MACHINE-CHECKED: rightmost reload-type steps with ANY second component (lean/FiniteHalfGen.lean, ns RG)
* lean/FiniteHalfGen.lean now also contains namespace RG (file 3,615 lines; recompiled by path, exit 0, 0 errors, no
  sorry; axioms propext, Classical.choice, Quot.sound).  RG.right_reload_detect_gen: a rightmost step
  t.sigma -> sigma.(q.sigma) (t with >= 2 arguments, sigma /= S) forces H(t) = S (S S) q.  RG.finite_half_right_general:
  a rightmost walk from an R19-flag-0 term never ends in computed nodes (t j).(s j) (s j /= S) whose steps are
  rightmost tail calls (s (j+1) = s j) or rightmost reload-type steps with ANY second component q
  (t (j+1) = s j, s (j+1) = q.(s j)).  Same proof pattern as FG: once size (s j) >= 6, top_rtc (a rightmost tail call
  from q.sigma forces q = S S, via R_strip) and top_rr (H(q.sigma) = S (S S) p forces q = S(SS), p = sigma) leave only
  q = S S; RR.finite_half_right excludes the canonical case.  So SF_R may be weakened in the same way (SF_R-).

## 08:37 EDT — MACHINE-CHECKED: Lemma Fib and the finite half for eventually MONOTONE walks (lean/FiniteHalfGen.lean, ns FM)
* lean/FiniteHalfGen.lean (now 4,045 lines; recompiled by path, exit 0, 0 errors, no sorry; axioms propext,
  Classical.choice, Quot.sound) adds namespace FM.  Towers: tw 0 = S, tw (m+1) = S (tw m); 'non-tower' = some
  right-spine multiplier is not S.
* FM.fib_step (Lemma Fib): if Q has >= 2 arguments, z is a non-tower and the head run of Q.z reaches [ch, d], then
  H(Q) = S (tw K) c0 and ch = Fw z c0 K, where Fw 0 = z, Fw 1 = c0.z, Fw (i+2) = Fw i . Fw (i+1).  So over a non-tower
  bottom every computed step is a 'Fibonacci step' (no refills).  Proof: chain invariant FM.J over the wrap history
  OM.WH — once the current head is a non-tower it stays one (a refill's first component is a spine-wrap of the
  current bottom, FM.first_suf; a peel keeps it), and a non-tower head can never end the chain.  (Cross-check
  fibcheck.py: 12,957 random instances, all Fibonacci.)
* FM.finite_half_monotone: an infinite leftmost walk from an L36-flag-0 term never ends in nodes (t j).(s j) with t j
  having >= 2 arguments (no pops, no jumps) and u (j0+j+1) /= s j (no step returns to its bottom), once the bottom s 0
  is a non-tower.  Proof: every step is Fibonacci with K >= 1 pushes; the top after a K-step is Fw (K-2); a top A.B
  with B a non-tower forces A = tw (K'+1) (FM.htop inside the proof); hence K >= 4 is impossible, a K = 3 step must be
  followed by a tail call with second component the old stack and leaves the stack (s j).(S(SS).(s j)), which can never
  become a top — but the next growing step makes it the top.  So all steps are tail calls or Omega-type steps, and
  FG.finite_half_general_families applies.
* Consequence: the leftmost finite half for flag-0 classes now follows from Conjecture EM (every infinite leftmost walk
  is eventually monotone: eventually no pops, no jumps, no returns k = 0) together with excluding monotone walks
  whose bottoms are towers S(S(...(SS))) forever (towers allow refills; not covered).  Remaining cases are therefore
  Scenario A (depth returns infinitely often), Scenario C (infinitely many jumps), Scenario B with infinitely many
  returns/pops, and the tower case.

## 08:42 EDT — MACHINE-CHECKED: no flag-0 term has an eventually monotone infinite leftmost walk (FM.finite_half_monotone_all)
* lean/FiniteHalfGen.lean (4,219 lines; recompiled by path, exit 0, 0 errors, no sorry; axioms propext,
  Classical.choice, Quot.sound).  FM.finite_half_monotone_all: an infinite leftmost walk from an L36-flag-0 term never
  ends in nodes (t j).(s j) with t j having >= 2 arguments and u (j0+j+1) /= s j — i.e. it is never EVENTUALLY
  MONOTONE (from some node on: no pops, no jumps, no step that returns to its bottom).  No hypothesis on the bottom.
* Tower case (FM.tower_grow): if a computed step from Q.z has a child A.B with A having >= 2 arguments, B a tower and
  B /= z, then size z <= 2 (the chain's last head is S S, its previous wrap is S or S S).  So over tower bottoms
  the bottom changes at most twice and is then fixed: FH.finite_half_TC.  Non-tower case: FM.finite_half_monotone.
* Status of the coordinator's task: the leftmost finite half for (14,28), (14,26) (indeed for every flag-0 class)
  now reduces to CONJECTURE EM: every infinite leftmost walk is eventually monotone — equivalently, it has only
  finitely many pops, jumps and returns (computed steps whose child is the node's own last argument).  Scenario A
  (stack depth returns to a fixed level infinitely often) and Scenario C (infinitely many jumps) are exactly the
  ways EM could fail, plus Scenario B with infinitely many pops/returns.  EM is EXPERIMENTALLY SUPPORTED by the same
  data as SF (2,051 infinite walks, 619,000 steps after burn-in: only tail calls and canonical Omega steps).

## 08:50 EDT — MACHINE-CHECKED: the rightmost analogue (RM) — R19's finite half reduces to 'eventually monotone'
* lean/FiniteHalfGen.lean (4,593 lines; recompiled by path, exit 0, 0 errors, no sorry; axioms propext,
  Classical.choice, Quot.sound) adds namespace RM.
* RM.fib_step2: over a non-tower bottom z, the head normal form of Q.z (Q with >= 2 arguments) is
  [Fw z c0 K, Fw z c0 (K+1)] where H(Q) = S (tw K) c0.  So the leftmost child is Fw K and the rightmost child Fw (K+1).
* RM.finite_half_right_monotone_all: a rightmost walk from an R19-flag-0 term never ends in nodes (t j).(s j) with
  t j having >= 2 arguments, i.e. it never eventually consists of nodes with >= 3 arguments (no rightmost step that
  drops a multiplier).  Non-tower bottoms: RM.finite_half_right_monotone (push counts P = K+1 >= 3 are impossible as in
  FM; P = 1 rightmost tail calls, P = 2 reload-type steps; RG.finite_half_right_general).  Tower bottoms
  (RM.rtower_grow): the bottom can change only from S, so it is eventually fixed and the walk is an R-chain — no
  flag needed.
* So R19's finite half reduces to CONJECTURE EM_R: every infinite rightmost walk eventually has only nodes with >= 3
  arguments (finitely many 1- or 2-argument nodes).

## 09:02 EDT — MACHINE-CHECKED: no infinite tower-headed chain; no Scenario A over a non-tower fuel (ns SA)
* lean/FiniteHalfGen.lean (4905 lines; recompiled by path, exit 0, 0 errors, no sorry; axioms propext,
  Classical.choice, Quot.sound) adds namespace SA.  No flag hypothesis in either theorem.
* SA.no_TT_chain: there is no sequence W0, W1, ... of closed S-terms with H(W_j) = S (tw K_j) W_(j+1) (any K_j >= 0).
  Generalises no_R_chain (K = 0) and no_R2_chain (K = 1).  Proof: some W_j has >= 3 arguments (else sizes drop);
  from then on W_j = Y_j.(tw m_j) with Y_j having >= 2 arguments (SA.TT_strip; otherwise the chain dies within two
  steps, SA.TT_dies), and each step is an R-step Y_j -> Y_(j+1) with the same tower, except that the tower may grow
  once from S to S S; so eventually an infinite R-chain.
* SA.no_scenarioA: no jump-free infinite leftmost walk (no node with exactly two arguments) keeps a non-tower Z as a
  proper right-spine suffix of every node and returns infinitely often to the level directly above Z (nodes q.Z).
  Proof: at a return q.Z the step is a Fibonacci step (FM.fib_step), H(q) = S (tw K) c with K >= 1 (K = 0 would
  reach Z); by SA.step_keeps the walk stays above c.Z until it is at c.Z, so the next return multiplier is c; the
  return multipliers form an infinite tower-headed chain.
* Consequence (PROVED from the two Lean theorems; the 'liminf' bookkeeping is on paper): in Scenario A (jump-free,
  stack depth returning infinitely often to its eventual minimum d*), the frozen part Z below level d* must be a
  tower S(S(...(S S))) — half of Conjecture F, which says Z = S.  EM can now fail only through Scenario A over a
  tower fuel, unbounded depth with infinitely many pops/returns, or infinitely many jumps.

## 09:08 EDT — MACHINE-CHECKED: the reductions in final form (ns EM)
* lean/FiniteHalfGen.lean (4949 lines; recompiled by path, exit 0, 0 errors, no sorry; axioms propext,
  Classical.choice, Quot.sound) adds namespace EM:
  - EM.finite_half_of_EM: for an infinite leftmost walk u from an L36-flag-0 term, the hypothesis
    'exists j0, for all j >= j0: u j has >= 3 arguments and u (j+1) /= (last argument of u j)' is contradictory.
    I.e. CONJECTURE EM => every flag-0 term (e.g. of (14,28), (14,26)) has a finite leftmost path.
  - EM.finite_half_right_of_EMR: same for the rightmost path, R19 flag 0 and 'eventually >= 3 arguments'.

## 09:09 EDT — Theorem map for lean/FiniteHalfGen.lean (4,949 lines; for the main agent; line numbers of the statements)
| Lean name (line) | statement (closed S-terms; LChild/RChildC = leftmost/rightmost step; flag = L36, flagR = R19) |
|---|---|
| EM.finite_half_of_EM (4927) | infinite leftmost walk, flag (u 0) = false, eventually (>= 3 args and child /= last arg) => False |
| EM.finite_half_right_of_EMR (4938) | infinite rightmost walk, flagR (u 0) = false, eventually >= 3 args => False |
| FM.finite_half_monotone_all (4145) | same as EM.finite_half_of_EM, stated with u (j0+j) = (t j).(s j) |
| FM.finite_half_monotone (3843) | the non-tower case (s 0 not a tower) |
| FM.tower_grow (4081) | growing step to a tower bottom with a >=2-arg top starts from a bottom of size <= 2 |
| FM.fib_step (3790) | Lemma Fib: non-tower z, Q >= 2 args, hnf [ch, d] of Q.z => H(Q) = S (tw K) c0, ch = Fw z c0 K |
| FM.first_suf (3683) | first hnf component of a list of length >= 3 is a right-spine wrap of its last element |
| RM.fib_step2 (4231) | Lemma Fib with the second component: d = Fw z c0 (K+1) |
| RM.finite_half_right_monotone(_all) (4285, 4519) | rightmost analogues; RM.rtower_grow (4478) |
| SA.no_TT_chain (4680) | no infinite chain with H(W_j) = S (tw K_j) W_(j+1) |
| SA.no_scenarioA (4823) | no jump-free infinite walk returning infinitely often to q.Z over a fixed non-tower proper suffix Z |
| FG.finite_half_Omega_general (3224), FG.finite_half_general_families (3355) | tail calls + Omega steps with any second component excluded for flag 0 |
| RG.right_reload_detect_gen (3407), RG.finite_half_right_general (3490) | rightmost reload-type steps with any second component excluded for flagR 0 |
Definitions: FM.tw (towers), FM.Tower, FM.Suf (right-spine suffix), FM.Fw / FM.Fc (Fibonacci words), SA.TT, SA.rpart.
All #print axioms lines at the ends of the sections report [propext, Classical.choice, Quot.sound].
