# agent_work_P LOG (parallel-evaluation universality agent)

## 2026-10-27 10:18 EDT start
Task: look for universal emulation by S under parallel (ReplaceAll-style) evaluation, or precise barriers. Deadline 15:00 EDT.

## 2026-10-27 10:35 EDT reading done; working picture
* Read PROOF.md (LZ/PL, time-to-data, CF, Master Reduction, CA, CA-par, transfer lemma, Lemmas 8-10, J), STATUS R34/43-47/63-65, PRIZE_ASSESSMENT rules, agent_work_U/LOG.md (it only says the clock channel was "argued contractive", no file).
* Working picture (to be proved below): under ReplaceAll every element at list position >= 4 evolves autonomously; elements interact only at the head. So a parallel run = the head machine on PROCESSES. An element x pushed at pass b that is opened at pass T delivers its hnf at pass max(T, b + h(x)) (h = its own parallel hnf time) -- a MAX-PLUS law -- while leftmost-outermost delivers at T + h_LO(x) (a sum). Control flow (Boehm tree) is identical (Prop. CF); what differs is timing (max vs +) and pre-evaluated syntax.
* Plan: (1) prove the max-plus law exactly (from Lemma LZ) and test it; (2) exact gadgets: join = max under ReplaceAll vs sum under LO, race gadget; (3) reduction: races + concurrency + polynomial-time processes would give universality via Hilbert's 10th problem / Krob (max-plus automata); find exactly which ingredient S lacks; (4) barriers that transfer to every order.
* ptools.py: helpers (direct ReplaceAll pass P from code/parallel_eval.py, head steps, tree calls/levels).

## 2026-10-27 10:41 EDT Lemma PJ (process lemma, max-plus law) -- PROVED from Lemma LZ; COMPUTATIONALLY CERTIFIED on 952 random instances
* Statement. Let the list at pass T be [x, r1, r2, r3, ...] with x = P^w(x0) (x0 has aged w passes) and let
  h = min{j : P^j(x0) is head-normal} >= 1. Then at pass T + 1 + j*, j* = max(0, h - w), the list is
  spine(P^max(w,h)(x0)) ++ [P^j*(r2), P^j*(r1.r2), P^(1+j*)(r3), P^(1+j*)(r4), ...].
  So x0's head normal form reaches the front at pass 1 + max(T, b + h) with b = T - w (the pass at which x0 began to
  age): opening an element is a JOIN with its own clock (max), whereas leftmost-outermost needs T + 1 + h_LO(x0) (a sum).
  If x0 never head-normalises, the front segment follows x0's own run forever and nothing below is ever opened again.
* Proof. Opening x costs one pass (LZ (i)): list_(T+1) = spine(x) ++ [r2, r1.r2, P(r3), ...], and spine(x) = x0's own list at
  internal time w. While x0's own list has >= 3 elements, LZ (i) applied to the whole list performs exactly x0's own
  step on the front segment and ages everything below by one pass (prefix property). Induction on j. QED
* Check: agent_work_P/maxplus_check.py (direct ReplaceAll passes, random x0 <= 12 leaves, random ages w, random rest):
  seeds 1-4, 600 trials each: 241 + 228 + 247 + 236 = 952 agree, 0 mismatches (the rest skipped: x0 already head-normal
  or no hnf within 60 passes).
* Next: Lean formalisation of the general time-change theorem (any ReplaceAll run = head run sampled at increasing
  times with every list element internally reduced) on top of lean/Standard.lean.

## 2026-10-27 10:45 EDT Theorem PT (ReplaceAll run = head run sampled at increasing times, elements reduced) -- MACHINE-CHECKED
* File: agent_work_P/lean/ParTime.lean (lean/Standard.lean, lines 1-370, verbatim, + the section 'Theorem PT').
  `cd code && python lean_check.py ../agent_work_P/lean/ParTime.lean` -> "exit 0, 0 errors, 5 theorems checked ...
  LEAN OK: no errors, no sorry"; axioms propext, Classical.choice, Quot.sound (hstepN_det: propext only).
* Definitions: `pass` = one ReplaceAll pass (rule tried at the root first; a matched redex S x y z becomes x z (y z)
  and x, y, z are not entered; otherwise recurse into function and argument) -- the same function as
  code/parallel_eval.step_fn and Lemma LZ; `passN n t` = n passes; `HStepN k t w` = k head (leftmost-outermost) steps.
* Theorems (all MACHINE-CHECKED):
  - `par_pass`: a pass is a parallel reduction step.
  - `pass_head_step`: if t is not head-normal, t -> u by exactly ONE head step and `pass t` is an internal parallel
    reduct of u (internal = inside the spine arguments, head redex untouched).
  - `pass_HN`: if t is head-normal, `pass t` is an internal parallel reduct of t.
  - `commute_one`, `commute_star`: internal parallel steps followed by k head steps can be replaced by >= k head steps
    followed by internal parallel steps (postponement with counting; uses `ipar_hstep`, `par_decomp` of Standard.lean).
  - `hstep_det`, `hstepN_det`: head reduction is deterministic.
  - `theoremPT`: for every t and n there are k and the (unique) k-th head reduct w of t such that passN n t has the
    same head and the same number of spine arguments as w, its spine arguments are position-wise reducts of w's,
    and k >= n as long as no pass j < n reached a head normal form.
* Meaning. Write sigma(n) = k. A ReplaceAll run is the leftmost-outermost head run SAMPLED at the increasing times
  sigma(0) < sigma(1) < ... (while no hnf), with every list element replaced by one of its reducts. So, under
  ReplaceAll: the list length, the head, and every list element up to reduction are those of the head run at time
  sigma(n); sigma(n+1) - sigma(n) - 1 = head steps that the opened element had already done while it waited (Lemma PJ).
  Everything order-dependent is therefore (a) the sampling sigma (timing) and (b) the syntax INSIDE list elements
  (their own autonomous evolution); control flow is the head run's (with Prop. CF at the Boehm-tree level).

## 2026-10-27 10:50 EDT Lemma LZ (prefix form) and Lemma PJ (max-plus law) -- MACHINE-CHECKED
* Same file agent_work_P/lean/ParTime.lean (section 'Lemma LZ (prefix form) and Lemma PJ'); lean_check: "exit 0,
  0 errors, 7 theorems checked ... LEAN OK: no errors, no sorry"; axioms propext, Classical.choice, Quot.sound.
* `pass_ext`: if u has head S and >= 3 spine arguments, pass (u r1 ... rk) = (pass u) (pass r1) ... (pass rk).
* `passN_ext`: if u's own run is not head-normal at times 0..j-1, then
  passN j (u r1 ... rk) = (passN j u) (passN j r1) ... (passN j rk): waiting elements evolve autonomously.
* `lemmaPJ`: if x0's own run is not head-normal at internal times w..w+j-1, then
  passN (1+j) (S (P^w x0) r1 r2 R...) = (P^(w+j) x0) (P^j r2) (P^j (r1 r2)) (P^(1+j) R)...  [list form: Lemma PJ
  of the 10:41 entry]. With h = first head-normal time of x0 and j = max(0, h - w), x0's hnf is at the front
  1 + max(0, h - w) passes after the opening: a MAX of the opening time and x0's own completion time.
* Status of Lemma PJ upgraded: PROVED (10:41) -> MACHINE-CHECKED (10:50); random check (952/952) kept as a test of
  the Python machinery against the definition.

## 2026-10-27 10:54 EDT Corollary PT-V (data placement is order-independent) -- MACHINE-CHECKED
* agent_work_P/lean/ParTime.lean, `corollaryPT_data` (+ `red_occ`, `redstar_occ`, `pw_occ`); LEAN OK (8 theorems
  printed, axioms propext, Classical.choice, Quot.sound).
* Statement: with data = opaque variables, after n ReplaceAll passes the list has the same head and length as the head
  run's list at the sampled time k = sigma(n) (k >= n while no hnf), and position by position the same data
  (`occ v` = 'contains datum v'). Reason: S-reduction neither erases nor creates variables.
* Meaning for universality: every combination of data that the ReplaceAll run produces (which data share a list
  element, and in which list order) is already produced by the leftmost-outermost head run at time sigma(n). The clock
  channel cannot put together data that the head run keeps apart, so the data-placement barriers of head runs
  (Lemma 8 counts, 'no writing into two live data', Theorem J's structure, Lemma 10's order of the data blocks) are
  constraints on ReplaceAll runs too, at the sampled times. What ReplaceAll adds is (a) timing (sigma; max-plus,
  Lemma PJ) and (b) syntax inside elements (their autonomous evolution).

## 2026-10-27 10:57 EDT Lemma 10 under EVERY evaluation order (multiway, ReplaceAll) -- MACHINE-CHECKED
* File agent_work_P/lean/Lemma10Any.lean = lean/Lemma10.lean (lines 1-400, #print lines dropped) + new section.
  lean_check: "exit 0, 0 errors, 3 theorems checked ... LEAN OK: no errors, no sorry" (axioms propext,
  Classical.choice, Quot.sound).
* `red_inv`: the Lemma 10 invariant read on whole terms (J2 t and Kt t; J2 of S e1..em contains J1 of the list) is
  preserved by EVERY single step S x y z -> x z (y z), wherever the redex is: `hstep_inv` (head steps, including a
  variable-headed x, which the list machine of Lemma10.lean never needed) and internal steps (`red_cases`,
  `J1_congr`: an internal step keeps the head and the (contains x, contains y) signature of every spine argument).
* `lemma10_any`: from the start S A X B Y C (A, B, C free of x and y; X free of y above Y free of x), in every term
  reachable by ANY reduction sequence, every y-headed subterm containing x contains y at least twice.
  `lemma10_replaceAll`: the instance 'after n ReplaceAll passes' (via `redstar_passN`).
* Meaning: 'no junk-free rotation' is not an artefact of leftmost-outermost evaluation; the clock channel cannot
  rotate two data cleanly either. Together with Corollary PT-V (data placement) the data-manipulation barriers that are
  invariants of single steps hold in every order; the ones that use frozen waiting elements (barrier lemma, access
  lemma, stale copies on the leftmost path) need not.

## 2026-10-27 ~11:03 EDT (between `date` readings 10:58 and 11:05) Clock-channel capacity: what a waiting element can transmit -- PROVED + EXPERIMENTALLY SUPPORTED
* PROVED (from Lemma PJ, MACHINE-CHECKED): a waiting element W opened at age w delivers exactly spine(P^max(w,h)(W))
  (h = first head-normal time of W's own ReplaceAll run) at pass 1 + max(T, b + h); nothing else in the future
  depends on w. Every delivered element is a ReplaceAll iterate of a fixed term, so the ONLY effect of the clock is a
  time shift of autonomous runs. Saturation: if P^N(W) is a normal form then D(w) = D(N) for all w >= N (passes fix
  normal forms), so a normalising clock carries at most N(W) + 1 values -- the channel is 'contractive' exactly for
  normalising clocks; a non-normalising clock can carry an unbounded age, but only as a shift.
* EXPERIMENTALLY SUPPORTED (agent_work_P/clock_capacity.py 9 40 20000 3000; all 2,056 S-terms <= 9 leaves; direct
  passes, horizon 40 passes, size cap 20,000; hnf refinement by <= 3,000 head steps):
  1,737 normalise within 40 passes (largest normalisation time 18) -> saturating clocks;
  5 reach an hnf and do not normalise within 40 passes, delivering 33-39 distinct contents in 40 ages (age-injective);
  314 hit the size cap: of these 163 have an hnf (head run ends), 151 have no hnf within 3,000 head steps (opening such
  a W hands the head to W's own run, shifted by w; nothing below is opened again).

## 2026-10-27 11:05 EDT Exact max/monus gadget with flat combs -- PROVED (Lemma PJ) + COMPUTATIONALLY CERTIFIED (1,600 pairs)
* D_d := the left comb S S ... S with d+3 leaves is a delay: its own run reaches the hnf S S comb(d+1) at internal time
  d (each pass consumes one S; ReplaceAll = head run here). Gadget M(d, e) := S D_d R D_e Y (any R, Y).
* Under ReplaceAll (Lemma PJ twice): D_e ages while D_d runs, is at the front at pass 2 + d with age d, and
  spine(P^max(d,e)(D_e)) = [S, P^max(0,d-e)(comb(e+1))] is laid out at the front at pass 3 + max(d, e). The opcode
  (spine length of the front element) at pass 2 + d is 2 + (e -. d) (monus). Under leftmost-outermost: the hnf
  [S, comb(e+1)] at step 3 + d + e, opcode e + 2.
* So ReplaceAll computes max and truncated subtraction of two programmed delays where leftmost-outermost computes the
  sum; the race outcome (e <= d or not) is visible in the opcode word. Check: agent_work_P/max_gadget.py 40 -> "1600 of
  1600 pairs (d, e) <= 40 agree with the predictions".
* What it does NOT give: by Prop. CF and Theorem PT the control skeleton (head run, Boehm tree) is the same for every
  (d, e) up to conversion; the comparison changes only timing and syntax. A counter machine needs the zero test to steer
  control, which no order allows. So timing arithmetic can only feed the detector: a universal emulation through it
  must let a fixed (data-blind) skeleton generate unboundedly many races whose outcomes the detector reads.

## 2026-10-27 11:08 EDT Corollary PT-F (ReplaceAll reaches an hnf no later than leftmost-outermost) -- MACHINE-CHECKED
* agent_work_P/lean/ParTime.lean, `corollaryPT_fast` (+ `HN_no_hstep`, `hstepN_split`); lean_check: LEAN OK, no sorry
  (axioms propext, Classical.choice, Quot.sound).
* Statement: if the head run of t reaches a head-normal term after h steps, then passN n t is head-normal for some
  n <= h. So h_par(t) <= h_LO(t) for every term (consistent with Lemma PJ: a join costs max instead of sum).
* With Lemma LZ (ii) (a pass on S a b is S (pass a) (pass b): the two arguments of a head normal form evolve
  independently and in lockstep) and induction on depth: every node of the Boehm tree of t is revealed by the
  ReplaceAll run after finitely many passes (PROVED, not formalised -- no Boehm-tree datatype in ParTime.lean).
  Leftmost-outermost reveals only the leftmost path (it never leaves an infinite leftmost subtree). Consequence for
  the Master Reduction: under ReplaceAll a detector 'some revealed node has property phi' is physically realisable for
  EVERY node, so detector class (D2) (existential Boehm-tree properties) is genuinely in play for this order; its
  non-universality still rests on C5' (open), not on anything order-specific.

## 2026-10-27 11:10 EDT Theorem PT-all (EVERY evaluation order = head run + internal reductions) -- MACHINE-CHECKED
* agent_work_P/lean/ParTime.lean, `factorization`, `theoremPT_all`; lean_check: LEAN OK, no sorry; theoremPT_all uses
  only propext, Quot.sound.
* Statement: for every reduction sequence t ->* u (any order, any path of the multiway system) there are k and the
  k-th head reduct w of t such that u is an iterated internal parallel reduct of w; hence u has w's head and spine
  length, position-wise reducts of w's spine arguments, and the same data at the same positions.
* Consequences (PROVED from the machine-checked pieces): (1) the data-placement content of the head-run barriers
  (Lemma 8 counts, Corollary 8(ii) / Lemma 9 (a) / Theorem J at a head normal form, Lemma 10) constrains every order
  and the multiway system: an hnf reached in any order is the leftmost-outermost hnf with internally reduced
  components (same data, same variable heads). (2) Everything an evaluation order can change is INSIDE list
  elements (internal reductions) and WHEN states are visited; the head machine's skeleton is universal to all orders.
* Exploratory (EXPERIMENTALLY SUPPORTED, tiny sample; agent_work_P/bt_reveal.py TERM 7): timed Boehm trees of the 5
  terms <= 9 leaves that head-normalise but do not normalise within 40 passes: off-path subtrees are revealed in the
  same pass as their parent (pre-evaluated while waiting); along the one infinite path the reveal-time increments are
  small and periodic (e.g. S(S(SS))(S(SS))(SS): reveal times 3, 5, 6, 8, 9 along 1, 11, 111, 1111). No max-structure
  beyond Lemma PJ visible at this size.

## 2026-10-27 11:12 EDT Transfer principle + monotone re-timing -- MACHINE-CHECKED; which head-run barriers transfer
* agent_work_P/lean/ParTime.lean now: 13 theorems printed, "LEAN OK: no errors, no sorry" (axioms propext,
  Classical.choice, Quot.sound; theoremPT_all, transfer_principle, factorization_mono only propext, Quot.sound).
  - `transfer_principle`: let dsig(u) = (head u, for each spine position the set of data in that element). Every
    property of dsig that holds for ALL leftmost-outermost head-run states of t holds for EVERY state reachable from t
    by any reduction sequence; `transfer_principle_replaceAll` is the ReplaceAll instance.
  - `factorization_mono`: along any run the head-run times of the factorisation can be chosen non-decreasing. So
    every evaluation order traverses the leftmost-outermost head run monotonically (pausing during internal steps)
    with elements internally reduced; an order can change WHEN head-run states are visited and the syntax inside
    elements, never the sequence of head-run states. This strengthens Prop. CF from head-normal-form events to
    infinite head runs.
* Transfer table (PROVED from the MC pieces unless marked; 'all orders' includes ReplaceAll and the multiway system):
  | head-run barrier | all orders? | reason |
  | Lemma 8 (data count), Cor. 8(ii), Lemma 9 (a), Theorem J (hnf structure) | yes | transfer_principle / PT-all; an hnf reached in any order is the LO hnf with internally reduced components |
  | Lemma 10 (no junk-free rotation) | yes, MACHINE-CHECKED | Lemma10Any.lean `lemma10_any` |
  | Theorem U* (no fuel created) | yes | 'closed element directly below data' is a dsig property |
  | Theorem H / H1-H3, Theorem N*, comb rigidity (BT level) | yes | Boehm-tree level (F5, CF) |
  | Access lemma / G1 (re-entry only with a second copy below) | yes up to reduction | positions are dsig; 'copy' becomes 'reduct of a copy' |
  | Barrier lemma (control reaches an argument before anything below is touched) | control part yes, freeze part NO | the head opens (reducts of) the same elements in the same order (PT); waiting elements are not frozen (R43, Lemma PJ) |
  | Lemmas 11/12, Theorem O cost bounds | NO for pass counts | passes <= head steps (Theorem PT k >= n; Cor. PT-F); costs transfer only to the re-timed head-step count |
  | stale copies / comb-like swaps on the leftmost path (agent U) | skeleton yes, syntax no | the leftmost path is reached in every order; contents of copies may be pre-evaluated |

## 2026-10-27 11:15 EDT Cross-check: the Lean `pass` is the project's Python ReplaceAll pass -- MACHINE-CHECKED instances
* agent_work_P/gen_pass_examples.py emits 30 `example : passN k t = u := by decide` (random t, 5-11 leaves, k = 1..4,
  u computed by code/parallel_eval.step_fn); appended to ParTime.lean (PassCheck section); lean_check: LEAN OK.

## 2026-10-27 11:15 EDT Theorem RR (race reduction): what a ReplaceAll universality proof would need -- PROVED (reduction)
* Setting: Wolfram's halting-style emulation (encoder, evolution, detector not itself universal).
* Theorem RR. Suppose there is a computable map (P, Q) -> t_(P,Q) from pairs of polynomials with natural coefficients in
  r variables to S-terms, and a fixed bounded-time pattern pi on subterm occurrences, such that the ReplaceAll run of
  t_(P,Q) (a) for every y in N^r creates a race node: a subterm S A_y B_y in a position where it evolves as
  S P^j(A_y) P^j(B_y) (an argument of a head normal form, or a waiting element), with h_par(A_y) = c + P(y) and
  h_par(B_y) = c + Q(y); pi matches such a node exactly when the left side is head-normal and the right side is not;
  (b) pi matches nothing else. Then 'some subterm matches pi' halts on t_(P_x,Q_x) iff x is in W, for any r.e. W
  (MRDP: x in W <=> exists y D(x,y) = 0 <=> exists y F+(x,y) < F-(x,y) + 1 with D^2 = F+ - F-), so S under ReplaceAll
  would be universal with a linear-time pattern detector.
  Proof: head-normal forms are stable under passes, so pi fires at node y iff A_y head-normalises strictly before B_y iff
  P(y) < Q(y); (b) excludes other matches. QED (MRDP cited.)
* Why this is the right target (from the machine-checked structure): no data-dependent CONTROL is needed (the
  comparison is done by the race and read by the detector), so Prop. CF / Theorem PT-all do not block it; durations of
  nested numeral calls are polynomial in the numerals (Theorem N: S(S S n P) has T = n T(P) + 2n + 3; CA-par keeps
  these times under ReplaceAll for normal-form arguments). What it needs is data-dependent CONSTRUCTION: for every
  tuple y the skeleton must insert the numerals of y into call templates. By Theorem PT-all and the transfer principle
  this is a question about leftmost-outermost head runs alone, and it is constrained exactly by the order-independent
  data-placement barriers: Theorem J (one closed layer per Boehm-tree step, wrapped around all live data), Lemma 10
  (machine-checked for every order), Theorem U*. One parameter (r = 1) is easy in principle but useless (exists y with
  P(y) < Q(y) is decidable for one variable); a non-separable duration such as y1*y2 needs an iterator for y2 whose
  body contains a call built from y1 ('data holding data' is allowed, but building the body from y1 while y2 is being
  incremented is a write into one of two live data). OPEN: whether a skeleton can build race pairs with non-separable
  polynomial durations for all tuples; no construction found in the attempt above (design sketch only, no search).

## 2026-10-27 11:18 EDT Theorem BC-par (ReplaceAll reveals every Boehm-tree node) -- MACHINE-CHECKED
* agent_work_P/lean/ParTime.lean, `replaceAll_reveals` (+ `node`, `revealed`, `pass_HN_exact`, `passN_HN_exact`,
  `node_forward`, `node_backward`, `replaceAll_hn`); lean_check: LEAN OK, no sorry (propext, Classical.choice,
  Quot.sound).
* `node t p`: the Boehm tree of t has a node at path p (some reduct head-normal, then recursively in argument p_i);
  `revealed u p`: u is already head-normal along p. Theorem: node t p -> exists n, revealed (passN n t) p.
  `passN_HN_exact`: on a head-normal term, j passes act argument-wise (head kept, args mapped by passN j): the
  arguments of a head normal form evolve independently and in lockstep.
* Meaning: ReplaceAll is Boehm-complete (fair); leftmost-outermost is not (it never leaves an infinite leftmost
  subtree). So under ReplaceAll a detector can observe ANY Boehm-tree node in finite time, and races between sibling
  subtrees are physically observable. Order-independent content (which nodes exist) is unchanged (F5/CF).

## 2026-10-27 11:24 EDT Exploratory probes for multi-parameter race durations -- inconclusive; memory incident
* numeral_products.py (write-free templates with two S-numerals, leftmost-outermost hnf times, n, m <= 5): within the
  caps the only 'non-separable' instances are boundary effects (T constant for n, m >= 2; e.g. N (M S) S: T = 5 for all
  n, m >= 2); several templates (N M S S for n >= 3, N M SS S) exceed the size caps. No genuine product durations
  found; the probe does not decide anything.
* Memory incident: the first run of numeral_products.py had no memory guard; its hash-cons table grew to 15.7 GB. Its
  bash wrapper was stopped (TaskStop) and the python process itself was killed by its own PID (94832, command line
  checked: 'python.exe numeral_products.py 6') at about 11:21. No other process was touched (tp_check.py PID 119604
  left running). The script now stops at 2,000,000 hash-cons nodes.
* Final re-checks (11:23): ParTime.lean "exit 0, 0 errors, 14 theorems checked ... LEAN OK: no errors, no sorry";
  Lemma10Any.lean "exit 0, 0 errors, 3 theorems checked ... LEAN OK"; maxplus_check.py 600 1 -> 241 agree, 0
  mismatches; max_gadget.py 20 -> 400/400.

## 2026-10-27 11:28 EDT Probe: junk of a reload head run as ReplaceAll processes -- EXPERIMENTALLY SUPPORTED (one term)
* junk_processes.py "S(S(SS))(S(SS))(SS)SSS" 120 (the E36 reload term with closed arguments): every product b.c pushed in
  120 head steps, run as its own ReplaceAll process, head-normalises within 0-5 passes independently of the cycle, or has
  no hnf within the caps (pushed at the opcode-4 steps). Natural junk here carries no parameter-dependent finite durations.

## FINAL (parallel universality agent) -- 2026-10-27 11:28 EDT

### Bottom line
No universal emulation by S under ReplaceAll (parallel) evaluation was found, and none is claimed. Instead the parallel
order is now pinned down by machine-checked theorems. A ReplaceAll run -- in fact every evaluation order and every path
of the multiway system -- is the leftmost-outermost head run traversed monotonically (re-timed), with every list
element replaced by one of its reducts (Theorems PT, PT-all). So the head-run skeleton and the placement of data are
the same in every order (Corollary PT-V, transfer principle), and Lemma 10 holds in every order. What ReplaceAll adds is
exactly: (a) waiting elements evolve autonomously, and opening one is a max-plus JOIN with its own clock (Lemma PJ);
(b) fairness: it reveals every Boehm-tree node (Theorem BC-par); (c) it is never slower to a head normal form
(Corollary PT-F). The clock channel can therefore change only WHEN head-run states are visited and the syntax INSIDE
list elements -- never the skeleton. A ReplaceAll universal emulation would have to be detector-mediated: a data-blind
skeleton that creates unboundedly many races whose outcomes a bounded-time detector reads. Theorem RR shows this would
suffice (via MRDP) and isolates the missing ingredient: race pairs with prescribed NON-SEPARABLE polynomial durations
for all parameter tuples, i.e. inserting several parameters into call templates -- a question about head runs alone,
constrained by the order-independent data-placement barriers. Open.
Rules (PRIZE_ASSESSMENT 'Rules', STATUS R34): a universality proof may pick any evaluation order. By Theorem PT-all
the choice of order can only re-time the leftmost-outermost skeleton and change syntax inside list elements, so picking
ReplaceAll (or any order) helps only an emulation whose detector reads timing or intermediate syntax; control-level
(skeleton-level) universality is the same question in every order.

### Constructed / proved (label; file; theorem names)
Lean files: agent_work_P/lean/ParTime.lean (= lean/Standard.lean lines 1-370 verbatim, then PT_tail, PJ_tail, PV_tail,
PF_tail, PA_tail, TP_tail, PM_tail, TM_tail, BC_tail, PassCheck_tail .lean.txt concatenated in this order) and
agent_work_P/lean/Lemma10Any.lean (= lean/Lemma10.lean lines 1-400 without its #print lines, then L10_tail.lean.txt).
Both: `cd code && python lean_check.py ../agent_work_P/lean/FILE.lean` -> "LEAN OK: no errors, no sorry" (last runs:
ParTime.lean 11:29, 15 theorems printed; Lemma10Any.lean 11:23, 3 printed); axioms propext, Classical.choice,
Quot.sound only. Both files are standalone (no imports).
1. Theorem PT -- MACHINE-CHECKED (`theoremPT`, `parallel_time_change`; tools `pass`, `pass_head_step`, `pass_HN`,
   `par_pass`, `commute_one`, `commute_star`, `hstepN_det`). After n passes the term has the head and spine length of
   the k-th head reduct w (unique by `hstepN_det`), its spine arguments are position-wise reducts of w's, and k >= n
   while no pass before n reached a head normal form.
2. Lemma LZ (prefix form) and Lemma PJ (max-plus law) -- MACHINE-CHECKED (`pass_ext`, `passN_ext`, `lemmaPJ`).
   Waiting elements age autonomously; for the list [P^w(x0), r1, r2, R...], the head normal form of x0 is at the front
   1 + max(0, h - w) passes after the opening (h = x0's own first hnf time): opening = max(T, b + h), while
   leftmost-outermost pays the sum. Random check of the list form: maxplus_check.py, 952/952 (seeds 1-4).
3. Corollary PT-V (data placement is order-independent) -- MACHINE-CHECKED (`corollaryPT_data`, `red_occ`).
4. Corollary PT-F (h_par <= h_LO) -- MACHINE-CHECKED (`corollaryPT_fast`).
5. Theorem PT-all, monotone re-timing, transfer principle -- MACHINE-CHECKED (`factorization`, `theoremPT_all`,
   `factorization_mono`, `transfer_principle`, `transfer_principle_replaceAll`, `transfer_monotone`): every state
   reachable in any order is an internal reduct of a head-run state, reached monotonically; every property of (head,
   data per spine position) that holds for all head-run states holds in every order, and every relation that holds
   between earlier and later head-run states holds between earlier and later states of any run (e.g. Lemma 8's
   non-decreasing data count; that instantiation is a hand step, Lemma 8 being machine-checked in lean/BarrierJ.lean's
   list framework). This extends Prop. CF from hnf events to infinite head runs.
6. Theorem BC-par (ReplaceAll reveals every Boehm-tree node; the arguments of a head normal form evolve in lockstep) --
   MACHINE-CHECKED (`replaceAll_reveals`, `passN_HN_exact`, `node_forward`, `node_backward`).
7. Lemma 10 in every evaluation order -- MACHINE-CHECKED (Lemma10Any.lean: `red_inv`, `hstep_inv`, `lemma10_any`,
   `lemma10_replaceAll`): no junk-free rotation of two data in any order or in the multiway system.
8. The Lean `pass` equals the project's Python ReplaceAll pass on 30 random instances -- MACHINE-CHECKED by `decide`
   (gen_pass_examples.py -> PassCheck_tail.lean.txt).
9. Exact max/monus gadget -- PROVED (Lemma PJ) + COMPUTATIONALLY CERTIFIED: with flat combs D_d (d+3 leaves, a delay of
   d passes), S D_d R D_e Y lays out D_e's hnf at pass 3 + max(d, e) under ReplaceAll (opcode 2 + (e monus d) at pass
   2 + d) versus 3 + d + e under leftmost-outermost (opcode e + 2). max_gadget.py 40: 1,600/1,600 pairs.
10. Clock-channel capacity -- PROVED + EXPERIMENTALLY SUPPORTED: a clock W opened at age w delivers exactly
   spine(P^max(w,h)(W)) (Lemma PJ), so its only effect is a time shift of autonomous runs; it saturates for normalising
   clocks (at most N(W)+1 values). clock_capacity.py 9 40 20000 3000 (all 2,056 terms <= 9 leaves): 1,737 normalise
   within 40 passes (largest time 18); 5 head-normalise without normalising and are age-injective (33-39 distinct
   deliveries in 40 ages); 314 hit the size cap (163 with an hnf, 151 without an hnf within 3,000 head steps).
11. Theorem RR (race reduction) -- PROVED as a reduction (MRDP cited): a computable family of terms whose ReplaceAll runs
   create, for every y in N^r, a race node S A_y B_y with h_par(A_y) = c + P(y) and h_par(B_y) = c + Q(y) (P, Q given
   natural-coefficient polynomials), recognisable by a fixed pattern, would make S universal under ReplaceAll with a
   linear-time tree-pattern detector (a finite tree automaton; if the finished processes have fixed shapes, even a word
   automaton on the serialisation, class D4 -- in that case it would also refute configuration-level R''_PUP there).
12. Transfer table (PROVED from 1-7; details in the 11:12 entry): Lemma 8, Cor. 8(ii), Lemma 9 (a), Theorem J at the
   hnf, Lemma 10 (MACHINE-CHECKED), Theorem U*, and the Boehm-tree-level barriers (H, N*, comb rigidity) hold in every
   order; the access lemma holds up to reduction; the barrier lemma's control part holds, its 'waiting elements are
   frozen' part does not (R43); the cost lemmas (11, 12, Theorem O) transfer only to the re-timed head-step count, not
   to pass counts.

### Refuted / corrected
* agent_work_U's note 'parallel clock channel argued contractive' (no file behind it): CORRECTED -- true for normalising
  clocks (saturation), false in general (age-injective clocks exist, item 10; R43's clock shows 6 distinct shapes); in
  every case the clock acts only as a time shift (Lemma PJ, Theorem PT-all).
* My own first join design via tree calls S C x y needs a pass-through hnf S S c; there is none among the contexts
  S C_m u v (w) with u, v, w <= 3 leaves (search_passthru.py: 0 found); flat combs provide it (passthru_scan.py 10:
  39 pass-through terms <= 10 leaves, the longest delays are the flat combs, h = leaves - 3).

### Open
1. The hypothesis of Theorem RR: can a data-blind skeleton build race pairs with non-separable polynomial durations for
   all parameter tuples (r >= 2)? Not blocked by Prop. CF (no data-dependent control is needed) nor by the
   data-blindness of calls (Theorem N gives products by nesting a numeral around a call); constrained by Theorem J
   (one closed layer per Boehm-tree step around all live data), Lemma 10 (every order) and Theorem U*. One parameter is
   easy and useless (decidable). No construction; the probes were inconclusive: numeral_products.py (write-free
   numeral templates: only boundary effects or size-cap overflows) and junk_processes.py (the E36 reload term
   S(S(SS))(S(SS))(SS)SSS, 120 head steps: every junk product pushed is a process with hnf time 0-5, independent of the
   cycle, or has no hnf within the caps; the same for the binary counter SSS(SS)S(SS(SS)), 400 head steps: 149 junk
   processes with hnf time 0, 57 with 1, 194 without an hnf within the caps, saved in junk_bc.txt -- natural junk
   carries no parameter-dependent finite durations; race material would have to be engineered).
2. Configuration-level R''_PUP for ReplaceAll (needed for D4 in the Master Reduction): now reduced to the head-run
   skeleton (Theorem PT) + max-plus re-timing (Lemma PJ) + the autonomous ReplaceAll runs of the list elements (the same
   kind of object, recursively). Open.
3. Detector class D2 under ReplaceAll: every Boehm-tree node is observable (Theorem BC-par), so existential Boehm-tree
   properties become ReplaceAll halting problems; their decidability is C5' (open, unchanged).
4. Krob route: do timed Boehm trees (reveal times, max-plus by Lemma PJ, with sharing from S's duplication) realise
   unboundedly ambiguous max-plus behaviour? Tiny sample (bt_reveal.py, the 5 terms of item 10): reveal times trivial
   (EXPERIMENTALLY SUPPORTED only). Open.

### Scripts behind the numbers (all in agent_work_P/)
ptools.py (helpers: the direct ReplaceAll pass of code/parallel_eval.py, head steps, tree calls); maxplus_check.py
(952/952); max_gadget.py (1,600/1,600); clock_capacity.py (2,056-term classification); passthru_scan.py (39 pass-through
terms <= 10 leaves); search_passthru.py (0 found); race_probe.py (call processes S C x y: the marker x.y first reaches
the front at T(C) = 6, 14, 30 for x = SSS, m = 1..3; direct passes hit the size cap near pass 30); bt_reveal.py (timed
Boehm trees); gen_pass_examples.py (30 kernel-checked pass instances); numeral_products.py (inconclusive probe, now
with a memory guard); junk_processes.py (junk products of a head run as ReplaceAll processes).
Incident: one unguarded run of numeral_products.py reached 15.7 GB; I killed my own process (PID 94832, command line
checked) at about 11:21; nothing else was touched.

### Suggested integration (for the main agent)
* STATUS: new rows for Theorem PT / PT-all / transfer principle (MACHINE-CHECKED), Lemma PJ (MACHINE-CHECKED), Theorem
  BC-par (MACHINE-CHECKED), Lemma 10 in every order (MACHINE-CHECKED), Theorem RR (PROVED, a conditional reduction),
  clock capacity (PROVED + EXPERIMENTALLY SUPPORTED); R43 scope note: 'the clock is only a time shift (Lemma PJ)'.
* PROOF.md, 'Control flow is order-independent': Proposition CF now extends to infinite head runs (Theorem PT-all,
  `factorization_mono`). Master Reduction ledger: 'configuration R''_PUP, parallel' -> reduced as in Open 2.
* code/verify_all.py: add the two Lean files (standalone).
