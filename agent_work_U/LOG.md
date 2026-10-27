# agent_work_U LOG (UNIVERSALITY agent, 2026-10-27)

Brief: construct a universal emulation by S alone (any evaluation order or multiway), with a non-universal
encoder/detector/decoder.  Labels: PROVED / MACHINE-CHECKED / COMPUTATIONALLY CERTIFIED / EXPERIMENTALLY SUPPORTED /
CONJECTURAL / REFUTED.  Deadlines (coordinator): INTERIM summary 04:00 EDT, refresh ~every 2 h, FINAL summary by 15:30 EDT.
All files of this agent live in agent_work_U/.

## 01:15 EDT start
* Read: PROOF.md (prize target, Theorem SI, U/U*, pump, write-pass, OT/OTD/SL, full re-execution frontier, bridge UB),
  agent_work/LOG.md, NEXT_STEPS.md head.  Tools: code/hc.py, code/symb.py, agent_work/hm.py.

## INTERIM 04:00 (written 02:40 EDT; supersedes nothing — first summary)
**Status: no universal construction; no partial win (no non-PUP run).  All results below are labelled.**
What I tried (all files in agent_work_U/):
1. NEW FRAMEWORK, the descent machine DM (dm.py): leftmost-outermost evaluation restricted to the leftmost Boehm path,
   i.e. the head machine plus the erasure rule [c, d] -> ch(c) at every head normal form (PROVED, elementary).  It is
   the one place where leftmost-outermost evaluation ERASES (the second hnf component is frozen for ever while the
   path stays infinite).  By Lemma P it is embedded in the head run of t A B, so it is 'full re-execution with
   erasure'.
2. DM capabilities (PROVED by inspection, checked by dm.py): Church booleans in tail position (S X Y => X,
   SS X Y => Y), clean application (S(SS) X Y => X Y), identity (SSSS X => X), unboxing ((S x) y => x), and the
   selection gadget S(SS)(SS) E b => b (E b) (E (SS E) b), which keeps the full state in both branches.
3. DM limits (PROVED elementary + COMPUTATIONALLY CERTIFIED in bounded ranges):
   - a round that keeps data ends [S, b, c] -> survivor c = the bottom element; the bottom only changes by wraps
     w.c with a stale copy left above, erased only if the wrap is the very last step: ONE closed wrap per round;
   - single-datum DM = a stack machine with pop / rewrite-top / branch-on-top, the stack never grows without copying
     the datum (growth1.py: 20,000 random runs, 0 growth);
   - two opaque data: every first round either executes a datum or erases all data (survcat.py, C <= 8 leaves); no
     round modifies one stack and keeps the other (twostack.py, h <= 8); 3-argument rules never erase and always pass
     the deepest argument through (headcat.py, lincat.py <= 8 leaves).
   Reading: the DM is pushdown-like (with copies, higher-order-pushdown-like) — it gives data-dependent SELECTION
   (which the head-run capability map lacked) but no second independent store.
4. Call-by-value / innermost view (cbv.py): by Prop. CF all orders share Boehm-level control; innermost syntax of a
   driver-built tower is the CBV iterate nf(G[x]).  Searches: CBV functions on unary values (cbvfun/cbvsize,
   a <= 9), CBV iterations (cbviter, f <= 7), CBV string transducers (cbvtrans, b <= 8): only affine sizes, exact
   linear recurrences, constant or fixed-prefix maps — non-erasure duplicates the argument at every distributive
   step.  (A size-cache bug in dm.truncate produced a false 'irregular' signal at 03:00; fixed and re-run.)
5. Word/round searches in DM and head runs (wordround.py, selfword.py, combhalve*.py): no fixed-format word rounds,
   no self-transforming words, no comb halving (q, v <= 6).
Strongest concrete result: the DM selection mechanism + the 'one closed wrap per round' lemma, which together
explain why leftmost-path programs are pushdown-like; no construction.
Next: (a) try to turn the single-datum stack machine plus datum copies (x1 (c x1)) into two counters, or prove the
2-datum obstruction in general; (b) parallel evaluation's clock channel (the only mechanism that changes a datum
below another without touching it).

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
