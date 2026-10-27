# PROVER_LOG (agent U, universality route) — running log, newest last

Labels: PROVED / COMPUTATIONALLY CERTIFIED / EXPERIMENTALLY SUPPORTED / CONJECTURAL / REFUTED.
Head machine: [a,b,c]++R -> ch(a)++[c, b.c]++R. Scripts: code/agent_u_*.py.

## Summary of earlier work (2026-10-25)
* Gadget (PROVED): [S(S P')V, t1, t2] ->2 [P', t2, V.t2, t1.t2] ("head-style" nest: predecessor first, closed constant
  after; one clean unit written into t2, duplicate t1.t2 sinks into a frozen tail).
* Phi(k,m) = S P_k S M_m (code/agent_u_transfer.py), rules R1-R3z (PROVED symbolically with opaque predecessors /
  tape elements; concrete checkpoints k<=8, m0<=5; M35 class 33). Program: while P>0{P--;M++}; while M>0{M--;Y++};
  while Y>0{Y--}; loop forever. Straight-line only.
* Theorem U (PROVED, audit 6 with fixes: needs initial F1/F2): no data element directly above a closed element; no data
  spine arg directly followed by a closed one. Lemma U3 (two-above blocking) PROVED. Random checks 0 violations.
* Generation bound: HEURISTIC; its slogan REFUTED by audit 6 (sawtooth below).
* Sawtooth (audit 6): t = S(S(SS))(S(SS))(SS)S; the single head run of t z z follows the infinite leftmost path (Lemma P);
  slot 2 = SS-nest counting down n-2..0, reloaded from slot 3, which gains one SS layer per cycle.

## Task now: rung (1) = looping program in ONE infinite head run with A--/B++ body and zero test re-entering the loop.

## 2026-10-25 entry 1 — sawtooth mechanism made exact (scratch tool sawsearch.py, nestwalk symbolic nests)
Node-level template u(i,k) = N_i N_k S (N = SS-nests over B = S(SS)(SS)); inside the single head run of t z z the front
element is u(i,k) at the start of each cycle. Exact symbolic transitions (case splits on i, k; tape w1, w2 opaque):
(i>=1,k>=1) -> (i-1,k) in 5 steps; (i>=1,k=0) -> (i-1,0) in 7; (i=0) -> (k,k+1) in 6. COMPUTATIONALLY CERTIFIED
(symbolic, all values) + concrete trace of t z z (steps 1..3000: templates at the predicted steps).
Mechanism: SS-iterator N_i a b -> a b (N_{i-1} a b) with body a = N_k (B used as code); the closed fuel S after N_k is
carried inside the frame N_{i-1}.N_k.S and re-released each cycle, so F1/F2 of Theorem U fail at the template (fuel
recycling) — this is how the reload escapes Theorem U.

## 2026-10-25 entry 2 — searches for an A--/B++ loop body (scratch saw2.py; bounded, symbolic, all values)
* Same-family node templates N_i . N_k . F (W <= 3 leaves, base <= 4, fuel F = none / one constant <= 3 leaves before or
  after B: 324 templates): every body transition (i>=1) has B-offset 0 [(i-1,0):166, (i-2,0):68, (i-3,0):68, (i-4,0):67];
  0 bodies with A--, B++. COMPUTATIONALLY CERTIFIED (bounded search).
* Two families, A = SS-iterator, B any wrapper/base <= 3 leaves, one or two fuel constants: B never changes (497 bodies,
  all (i-j, k+0)). COMPUTATIONALLY CERTIFIED (bounded).
* Frame lemma (PROVED, from the blocking lemma): if a node A.X1..Xr is opened at the front and A's predecessor is the
  topmost element containing A's core, then until that core is opened every element below it is an original X_j / tape
  element (unchanged) or contains A's core. Hence the next node's arguments are old arguments or A-compounds: a counter
  carried as an argument of A's frame cannot change during A's countdown. B can change only when a CLOSED element is
  opened with B the topmost datum (Theorem U(b)) — in the sawtooth this happens exactly at A = 0 (the base S(SS)(SS)
  WRAPs N_k: [SS,SS,N_k,S] -> [S,N_k,SS.N_k,S]), i.e. once per outer cycle, not per decrement.
* Larger same-family scan (sawscan.py: W <= 4 leaves, base <= 5, fuel lists of 0-2 constants <= 3 leaves after B; 4,347
  families, 120-step budget): 0 families with an A--/B++ body plus a terminating reload. COMPUTATIONALLY CERTIFIED (bounded).

## 2026-10-25 entry 3 — rung (1) status: BLOCKED for the two architectures tried (report sent to coordinator)
(a) counters as frame arguments (sawtooth style): frame lemma (PROVED) => B constant during A's countdown; B can only be
    written by a closed base at A = 0 (once per outer cycle). (b) counters on the tape (Phi style): a clean B++ at an
    opening of a data element needs a closed constant directly below that element (an F1 violation = "fuel"); Theorem U
    (applied to the active prefix) says fuel is never created; Phi spends fuel built into the CLOSED program P, the
    sawtooth recycles one fuel per cycle without spending it; a reload that rebuilds a fuel-carrying A from data B is
    excluded when the active prefix at A = 0 satisfies F1/F2 (PROVED for Phi's prefix [B1, M_half, M_full]); the general
    "spend + recycle in one cycle" impossibility is ARGUED, not proved. Open loophole: entangled designs where B holds A
    (every B-element contains A's core), where neither Theorem U's corollaries nor Lemma U3 apply.

## 2026-10-25 round 2 — task: rung (1) via (A) fuel splitting, (B) entangled, (C) Fibonacci reload sources
Inputs from disprover: Corollary W (clean write onto y only when no element contains x without y), fuel splitting (F2:
code/hsdepth.py), backward analysis of writes behind a live control (j=1 target holds fuel; j=2 head-style control;
j>=3 entangled source).
* (A) first search (fuelsearch.py, scratch): frame = A_i . fuel (A wrapper nest, fuel 0-2 constants <= 3 leaves),
  tape slots from {B, junk, constant} (8 shapes), A, B wrappers <= 3 leaves: 21,043 branches; 44 full template
  recurrences, ALL of type (i-1, k+0) (B unchanged); 0 A--/B++ bodies. COMPUTATIONALLY CERTIFIED (bounded).
  Wrapper nests cannot express the j=1 route (B holds fuel: layer y -> V.(y.V)); next: general layer contexts.
* New tool code/agent_u_ctxnest.py: exact symbolic head machine for counters with ARBITRARY layer contexts ctx[#]
  (value n = ctx^n[base]); self-tests reproduce the sawtooth rules and agent-U rule R1 exactly.
* (A)/(C)-prep scan, same family for A and B (so a reload could copy), all contexts <= 5 leaves (98), list templates
  [A_i, slots..] with slots from {B, junk, constant} (14 shapes): 17 recurrences, all (i-1, k+0); 0 A--/B++ bodies.
  COMPUTATIONALLY CERTIFIED (bounded). Two-family scan (contexts <= 4 leaves) running.
* (C) concrete scan (fibreload.py, scratch): S-nest countdown with the fuel-free Fibonacci body [S N, t1, t2] ->
  [N, t2, t1.t2] (A-- with a self-compound B-step), base B0 <= 6 leaves, tape constants Q, V <= 3 leaves, j = 1..4,
  400 steps: 0 bases that reload to [S^(m) B0, Q, V]. EXPERIMENTALLY SUPPORTED negative (bounded). Reason (argued):
  rebuilding A needs reading the Fibonacci words, whose letters are the tape constants; restoring closed Q, V directly
  below the rebuilt A is never observed.
* (A) analysis (ARGUED, not proved): with B on the tape, a wrap increment (V,B) -> (B, V.B) leaves the old copy in
  front; its sink twist (B, V.B) -> (V.B, B.(V.B)) always places the junk DIRECTLY below the new value, so any fuel that
  sat below B is cut off from it. An append increment (B,c) -> (c, B.c) is copy-free but consumes the closed element
  directly below B; the (F2) split [a,B,c,R1] -> [..,last(ch a), c, B.c, R1] moves the fuel copy to the opener side
  (where the next twist consumes it as a wrap), never back below B. Net: one closed element below B lost per pass.
* (B) analysis (ARGUED): with Corollary W, a clean write onto B needs every A-element to contain B; the only way found
  is A_pred absorbing B (A holds old B) and writing B's copy; the copy then sits above the A-frame with the old copy
  (Lemma U3: two y-only elements above the x-frame) and must be released by opening the old copy, i.e. a full re-read
  of B per pass, after which the new B holds the A-frame which holds the stale B (nesting grows each pass).
* Node-template corollary of the frame lemma (PROVED): if the counters live in the spine of the node at the front and a
  pass does not open the head's core, the next node's arguments are old arguments or head-compounds. Hence: head = A
  (A holds B) -> B unchanged; head = B (B holds A) -> A's slot can change only by acquiring head-compounds (stale copies
  of B's frame appended); a decrement of an argument counter happens only on a COPY above the frame (as the sawtooth
  does with N_k), and its predecessor can re-enter the node only as a frame-compound (A_pred . frame = junk-carrying).
  So no clean A--/B++ pass exists in node templates; the head changes identity only when its core is opened (zero test).
* Engine check: agent_u_ctxnest reproduces the AB transfer with ctx_A = S(S#)S, ctx_B = S# ((i,k) -> (i-1,k+1) in 2
  steps), so the two-family scan (running) would detect Phi-type bodies. Such bodies need fuel w.r.t. A's core x (the
  opener S P' is x-data directly above closed V) but are fuel-free w.r.t. B's core y; F1/F2 for y alone are NOT
  invariant (an x-violation can create a y-violation: [a(y), b(x only), c closed] -> last(ch a) above c), so the
  'target holds fuel' route (F3, j=1) is not excluded in principle — but the x-fuel of a closed program is used up as
  A counts down, and nothing found converts it into y-fuel stored in B. Head-style same-family scan (contexts <= 6
  leaves with a closed argument after the hole, 4-slot tapes with fuel below B) running.
* (A) scan with general A contexts (fuelctx.py, scratch; ctx_A <= 4 leaves (28), B = wrapper ctx V.# (V <= 3 leaves),
  frame fuel lists (9), tape shapes (6); 6,048 templates): 3 A--/B++ bodies, all exact 2-step rules, ALL head-style
  w.r.t. A's own core (a closed S directly after the predecessor inside A's layer):
    A_i = S(S(A_{i-1} S)), frame A_i.S, tape [J, B], B_{k+1} = S.B_k;   A_i = S(S A_{i-1} S), tape [S, B];
    A_i = S(S A_{i-1})S (the AB gadget), tape [J, B].   COMPUTATIONALLY CERTIFIED (symbolic, all values).
  j=1 route test (B layer V(#V), i.e. target holds fuel; ctx_A <= 4 leaves, 18 tape shapes with fuel below B): 0 bodies.
* Reload obstruction for this class (PROVED via Theorem U): at A = 0 only B's data remain (one variable y), F1/F2 hold
  (B is twist-built, constants sit above data), so by Theorem U no value with a y-data spine argument directly followed
  by a closed one ever forms: A cannot be rebuilt in head-style form from B, so the loop cannot re-enter a clean transfer.
* Same-family HEAD-STYLE scan (hsscan.py, scratch: 155 contexts <= 6 leaves with a closed argument after the hole,
  14 tape shapes with fuel constants below B, 60-step budget): 0 template recurrences of any kind, 0 A--/B++ bodies.
  COMPUTATIONALLY CERTIFIED (bounded). (A reload by copying needs A and B in one family; none of those families even
  recurs.)
* Two-family list-template scan (contexts <= 4 leaves both) stopped after ~55 min without output (it can only re-find
  Phi-type head-style bodies; not needed for the conclusion). Scan scripts copied to code/agent_u_{ctxscan,fuelctx,
  hsscan,fibreload}.py (engine: code/agent_u_ctxnest.py).
## round 2 conclusion: rung (1) BLOCKED for designs (A), (B), (C) in the searched/argued scope (report sent).
* Addendum: the two-family scan had in fact completed (captured by the monitor): contexts <= 4 leaves for A and B,
  list templates [A_i, slots]: 140 recurrences (i-1, k+0), 2 A--/B++ bodies, both head-style w.r.t. A's core:
  A_i = S(S A_{i-1} S) with tape [S, B], and A_i = S(S A_{i-1})S (AB gadget) with tape [J, B], B_{k+1} = S.B_k.
  COMPUTATIONALLY CERTIFIED (bounded); consistent with the round-2 conclusion (reload excluded by Theorem U).

## 2026-10-25 round 3 — task: route (1) under Lemma G1 (supply of closed constants below B), then entangled tape designs
Idea being tested first: let the SUPPLY itself be counter A (a run of n copies of S below B's lowest element). An
S-pump [S, B, S, ..., S, M, R] -> ... makes B absorb one S per step (A--, B++ per pass); the marker M ends it
(data-driven zero test); re-entry must spill B (an appending counter) to re-create a supply below a new target.
* Pump ping-pong (concrete scan pump1.py, scratch): template [S, X, S^n, M] recurs for 66 small (X, M) — but the trace
  (X = SS(SSS), M = SS, n = 3) shows the TARGET BASE DESCENDS: each round B = X.S^n.M.M is spilled and the next target
  is last(ch X) (SS(SSS) -> SSS -> S -> ...), then the count breaks. Exact pass rule (PROVED, 1 step each):
  [S, X, S, rest] -> [S, X.S, rest] (target absorbs one supply S = A--, B++), marker ends the pass (zero test), spill of
  B re-creates the supply directly below last(ch X). Obstruction (PROVED for spill re-entry): the next target is a spine
  argument of the current target's head (or its first absorbed element, which is a supply S) — a finite descent.
  Next idea: let the target bases be an SS-nest N_k (spine [S, N_{k-1}]) so rounds are (k, n) -> (k-1, n), and look for
  a base that re-enters with k' >= 1 (sawtooth-style reload of the base nest).
* Re-entry scan (pump2.py, scratch): target bases = SS-nests over B0 (B0 <= 6 leaves), markers M (2-4 leaves), R <= 3
  leaves, supplies n = 1..3, 500 steps: 0 cases where the k = 0 phase re-enters [S, N_k', S^m, M] with k' >= 1.
  EXPERIMENTALLY SUPPORTED negative (bounded).
* Pump round rule (PROVED, induction on the 1-step pass [S, T, S, R] -> [S, T.S, R] plus 4 marker steps, M = SS):
  [S, X, S^n, SS, SS, R] ->^{n+4} ch(X) ++ [S^n, SS, SS, R, (SS.(X S^n SS SS)).R]. With X = N_k (SS-nest, k >= 1):
  T(k,n) -> T(k-1,n): a loop that returns to the pump phase k times, each time n passes of A--/B++ (A = supply,
  B = target) with the marker as zero test; finite because the target base descends. Trying to put a sawtooth outer
  counter N_K between target and supply so that the k = 0 base reloads k := K (sawtooth reload).
* Pump round rule concretely checked: T(k,n) = [S, N_k, S^n, SS, SS, SSS] -> T(k-1,n) in n+4 steps for all k <= 5,
  n <= 5 (prefix equality at every round). COMPUTATIONALLY CERTIFIED (concrete) + PROVED (symbolic induction).
* Outer counter attempts: N_K between target and supply breaks the pump (symbolic, no recurrence, n = 1..3); bases
  B0 <= 7 leaves reloading the target nest from an outer counter N_K placed after the markers (pump3.py): 0.
  EXPERIMENTALLY SUPPORTED negative (bounded).
* Placement lemma (PROVED): opening a over (d2,d3) gives ch(a)++[d3, d2.d3]++R, so all material released from a lies
  ABOVE d3 and d2.d3. Closed material released by a control can sit directly below a target only if that target is an
  EARLIER spine argument of the same opened element; a target built from c / b.c of the control's opening lies below
  all of the control's released material. With Lemma G1 (supply below B's lowest element only shrinks until that
  element is opened, and its opening re-releases what it absorbed after its head's spine), the next target in any
  spill re-entry is a spine argument of the current target's head or its first absorbed element: a finite descent.
## round 3 conclusion: route (1) gives an exact FINITE loop (k rounds); infinite re-entry blocked by the descent;
## route (2) (entangled tape, inert stale copies) not constructed. Scripts: code/agent_u_pump{1,2,3}.py.

## 2026-10-25 round 4 — task: reverse transfer n -> k (supply into a head counter) or a reload at k = 0
Input (main agent): head-style targets X_k = S S X_{k-1} S make the pump round T(k,n) -> T(k-1,n+1).
Plan: exact symbolic search (agent_u_ctxnest, symbolic k, concrete n) over layer contexts <= 6 leaves and short closed
control prefixes P: template [P, X_k, S^n, SS, SS, r], looking for [P, X_{k+d}, S^{n-e}, SS, SS] with d, e >= 1.
* Stale-residue lemma (PROVED, from Lemma 2(c) + leaf monotonicity): after a write [a, V, X, R1, ..] -> ch(a) ++
  [X, V.X, R1, ..] the list is P ++ [Y] ++ R with Y = V.X the new value and P containing the stale copy X. The run of
  P ++ [Y] ++ R first performs the run of S.P: either it diverges (Y is never reached again: the loop dies), or it
  reaches the hnf list h of S.P (<= 2 elements) and continues from h ++ [Y] ++ R, with |S.h| >= |S.P| >= |X| (Lemma 1).
  So the residue directly above Y always has size >= the stale value; with |h| = 2 the next step wraps Y by h2 (a
  stale-derived layer), with |h| = 1 it appends R1 to Y and runs h1's stale-derived code. A reverse pass with a FIXED
  closed control above Y is therefore impossible for unbounded k; a pass whose control is the residue itself (a
  k-indexed family) is not excluded. Exact symbolic search over contexts running (code/agent_u_reverse.py).
* Symbolic traces (k symbolic, positive branch) of write + stale execution, start [S, SS, X_k, S, S, SS, SS, r, w], for
  the three suggested layer shapes: SSxS: the write gives [X_k, SS.X_k, S, S, ..] and executing the stale copy gives
  [S, X_{k-1}, S, S, X_{k+1}, S, SS, SS] (new value formed), but the stale cascade is a forward pump that absorbs the new
  value (step 5: [X_{k+1}, (X_{k-1} S S X_{k+1}), ..]) and re-executes it; the pattern then repeats with junk growing
  (k-1, k-2, k-3 ... cascades). SSx(SS) and S(Sx)S: the stale copy counts down to the base, each layer leaving junk
  between the front and the new value. In all three the stale residue sits directly above the new value (consistent
  with the stale-residue lemma). EXPERIMENTALLY SUPPORTED (exact symbolic traces, 22 steps).
* Concrete follow-up (SSxS over S(SS)(SS), start [S, SS, X_k, S^n, SS, SS, SSS, SSS], k, n <= 4, 4000 steps): the run
  never returns to a forward template [S, X_m, S^p, SS, SS] nor to a reverse template [S, SS, X_m, S^p, SS, SS].
  EXPERIMENTALLY SUPPORTED: one write + stale execution destroys the counter structure.
* Write-pass theorem (PROVED; Lemma 7(i), Lemma 2(c), leaf monotonicity): a pass that increases the NESTING depth of a
  counter Y must create the new value as b.c with c containing the old value, so a stale copy of the old value lies
  ABOVE the new value. Let the template demand a fixed closed control list C directly above the final value and the
  supply directly below it. After the last step that modifies the final value, every element above it is either C's
  material or stale material; nothing can pass below the value without absorbing it (Lemma 7), so the prefix above the
  value runs (Lemma 2(c), never touching the value) from P (containing stale material of size >= |old value|) to C,
  hence |S.C| >= |S.P| >= |old value| (Lemma 1). So no uniform reverse pass (supply -> nesting, or rebuilding a
  head-style OR wrapper-style counter of growing size from the supply) exists with a fixed control. If the stale copy
  instead absorbs the new value, the junk lands directly below the value, between it and the supply, and can move down
  only by absorbing supply elements one by one, breaking the supply's contiguity. Not excluded: controls whose size grows
  with k (the residue carrying a copy of the counter) — traces and the concrete search found none.
* CORRECTION (audit 9): my round-3 'placement-lemma consequence' (next target after a spill = spine argument of the
  head or the first absorbed S) is FALSE: the next target can be any absorbed element (e.g. [S,S,S,S(SSS),S]).
  REFUTED as worded. The placement lemma itself (released material lies above d3, d2.d3) stands.
  Following the coordinator: try to let each round's target absorb a fresh successor (sawtooth-generated N_k).
* Generator placement test (agent_u_ctxnest, symbolic i, K; n = 1, 2): target N_i (SS-nest) with a sawtooth
  generator N_K placed (a) before the supply, (b) after the supply, (c) between the markers, (d) after the markers.
  (c), (d): exact round T(i,K,n) -> T(i-1,K,n) (the generator rides along unchanged) — COMPUTATIONALLY CERTIFIED
  (symbolic); at i = 0 no re-entry (budget). (a), (b): no recurrence: a non-S element absorbed mid-pump has its copy
  executed above the target. Argument (stale-residue lemma again): the pump continues uniformly only if the element
  directly above the target is the opener S; absorbing G != S leaves a residue of size >= |G| there. Since the spill
  releases absorbed elements in absorption order, a successor target must be absorbed BEFORE the supply, i.e. mid-pump
  at the round start — so promotion of a generator to the next target breaks uniformity. ARGUED (not a full proof).
* Fixed-prefix reverse search (code/agent_u_reverse.py, contexts <= 5 leaves, 20 control prefixes, n = 1, 2) stopped
  after ~50 min WITHOUT finishing (no output). By the write-pass theorem it can only find passes that do not increase
  nesting; not used as evidence.
## round 4 conclusion: reverse transfer n -> k with a fixed control: PROVED impossible (write-pass theorem); reload
## via a successor absorbed from below: generator rides along exactly but cannot be promoted (argued + symbolic tests).

## 2026-10-25 round 5 — full re-execution regime: sawtooth variants with a third counter
Plan: node templates N_i . N_k . F_m (sawtooth with the fuel S replaced by a counter F_m of a small family; the fuel is
re-executed every countdown pass), exact symbolic search over F contexts <= 4 leaves and bases <= 3 leaves.
* Sawtooth with a third counter in the fuel slot (code/agent_u_saw3.py: node N_i . N_k . F_m, F contexts <= 4 leaves,
  bases <= 3 leaves, symbolic i, k, m): only two transition types occur: (i-1, k, m) [745 branches] and the reload
  (k, k+1, m) [731]; m NEVER changes (the fuel counter is re-executed every pass — full re-execution, step counts grow
  with m — but restored). COMPUTATIONALLY CERTIFIED (symbolic, bounded family). Consistent with the frame lemma (m is
  a frame argument) and U(b) (at the reload only the topmost datum N_k can be written).
* Sawtooth node N_i . X . c with X a counter of ANOTHER family (contexts <= 4 leaves, bases <= 3, possibly holding one
  junk argument), c in {S, SS} (code/agent_u_saw4.py): only countdowns (i-1,0) 406, (i-2..-4, 0) 48 branches; B never
  changes; 0 transfers; no reload recurs (A := B needs one family). COMPUTATIONALLY CERTIFIED (bounded).
* Three-slot sawtooth N_i . N_y . N_z (one SS family, bases B0 <= 7 leaves, code/agent_u_saw5.py): reload transitions
  only (y, y+1, z) [15], (y-1, y+1, z) [2], (y, y+2, z) [2]; z NEVER changes or moves. COMPUTATIONALLY CERTIFIED
  (bounded). Reason (U(b)): the closed base can write only onto the topmost datum (slot 2); slot 3 lies below it.
* 8-leaf bases for the three-slot sawtooth: one base S(S(SS)(SS))(SS) gives the reload (0,y,z) -> (y, y+1, y+1)
  (z overwritten by a copy of y+1, old z dropped); all others leave z. Still no transfer. COMPUTATIONALLY CERTIFIED.
* Frame-control templates [F[N_k], M_m, c] and [F[N_k], c, M_m] (F contexts <= 5 leaves, c in {S, SS}, SS-nests,
  code/agent_u_frame.py): no template recurrence at all within 60 steps. COMPUTATIONALLY CERTIFIED (bounded).
## round 5 conclusion: in the full re-execution regime explored (sawtooth-type nodes with a re-executed fuel counter,
## second-family B, three slots with reload bases <= 8 leaves, frame controls F[N_k] <= 5 leaves) the only loops are
## countdown + reload incrementing ONE counter; third counters are kept or overwritten by copies; no transfer found.

## 2026-10-25 round 6 — combine the reload loop (sawtooth) with the transfer gadget, candidates (a)-(d)
Sawtooth pass, exact (node u = N_i N_k S at the front over tape (t1, t2, ..)): 5 steps; the node's opening twists
(t1, t2) -> (t2, t1.t2); the B-copy residue (N_{k-1} S) absorbs the next frame, so the new tape front is
J = (N_{k-1} S).frame (junk) and t2 stays at position 2 forever. Candidate (a) needs a clean V directly below the frame.
* (a) sawtooth + tape counter (code/agent_u_sawtape.py: node N_i N_k V, fuel V <= 3 leaves, tape counter C of any
  family ctx <= 3 leaves, 6 tape layouts): full matches only (i-1, k, C) [8] and reload (k, k+1, C) [8]; C never
  changes. COMPUTATIONALLY CERTIFIED (bounded). Exact reason (PROVED from the 5-step pass): the only tape interaction
  per pass is the node opening's twist (t1, t2), and t1 is always the previous pass's residue J = (N_{k-1} V'). frame
  (the stale B-predecessor must absorb the frame to clear the region above it — Lemma U3 with one element above), so
  every tape write is a data.data compound (junk . t2); t2 is copied unchanged. => (a) blocked.
* (b) head-style countdown in the sawtooth node (X_i = S S X_{i-1} S, symbolic trace, B = X_k same family): node
  X_i . S . X_k . S passes to X_{i-1} . S . S . X_k . S — the recycled fuel S accumulates in the frame. Template
  T(i, n, k) = X_i . S^n . X_k . S: one pass (i, n, k) -> (i-1, n+1, k) (A-- and supply++, B unchanged as the frame
  lemma demands). EXPERIMENTALLY SUPPORTED (symbolic trace, two passes); exact rule to be certified. Next: reload at
  i = 0 (bases B0 <= 7 leaves).
* (b) pass rule CERTIFIED symbolically (code/agent_u_hsaw.py, all bases B0 <= 6 leaves, n = 1, 2: 228 branches, all
  (i, n, k) -> (i-1, n+1, k)): a head-style countdown A transfers into a supply S^n carried inside the frame
  (A-- / C++ per pass, C = supply). Reload at i = 0: 0 re-entries into X_a . S^p . X_b . S for bases <= 6 leaves.
  Running bases <= 8.
* (b) reload search, same head-style family for A and B, bases B0 <= 8 leaves (code/agent_u_hsaw.py 8 2): pass rule in
  all 2,044 branches; 0 re-entries from i = 0 into any X_a . S^p . X_b . S. A marker between supply and B breaks the
  countdown (24/24 tested markers <= 4 leaves). COMPUTATIONALLY CERTIFIED (bounded).
* (b) pass rule certified symbolically for X_i = S S X_{i-1} S^r, r = 1, 2, 3, body X_k (same family) or N_k (SS-nest),
  supply n = 0..4: every branch (i, n, k) -> (i-1, n+r, k), step counts linear in n (e.g. r=1, body X: n+7 / n+8).
  COMPUTATIONALLY CERTIFIED (symbolic in i, k; concrete n). This is the main agent's 'C += r per pass'.
* (b)/(c) observation (concrete traces, base S(SS)(SS)): a supply S^n in front of a head-style B = X_k (list
  [S^n, X_k, S, SSS, SSSS]) — for n = 1 the list is a pump-round template: B's depth transfers into the supply
  ([S, X_3, S^2] -> [S, X_2, S^2..] -> [S, X_1, S^3] -> [S, X_0, S^4], 9 steps per round) — for n >= 2 the leading S's
  collapse into a comb W = S S..S that wraps B (W.X_k) while a copy of X_k is executed at the front: a sawtooth-like
  'A := copy of B, B := W.B'. Testing base B0 = S for an infinite reload pattern.
* Base S for the head-style sawtooth (X_0 = S): concrete runs 20,000 steps: (3,2) settles into a PERIODIC pattern of
  front head depths [3,2,1,1] (no growth, junk grows linearly); (2,1), (2,3) leave the X-headed regime after a few
  events. EXPERIMENTALLY SUPPORTED: no growing re-entry.
* Trying head-style layers whose recycled fuel lands AFTER B (node X_i . B . F . S^n), so that the base meets B first.
* Layers putting the recycled fuel AFTER B (node X_i . N_k . F . S^n, all contexts <= 6 leaves, F in {S, SS}, n = 0, 1):
  only (i-1, k, n) [21] and (i-1, k, n-1) [21]; no context makes the supply after B grow. COMPUTATIONALLY CERTIFIED.
## round 6 conclusion: deliverable (i) NOT reached. Best partial: exact transfer pass A -> supply inside the sawtooth
## frame (head-style A, C += r per pass, certified r = 1..3); every reload attempt fails at the supply sitting in front
## of B (bounded searches + traces); candidate (d) not attempted.
