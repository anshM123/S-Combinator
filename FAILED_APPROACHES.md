# FAILED / INVALIDATED APPROACHES

1. **"Terminating head reductions open every origin at most twice"** (route to the linear bound C2).
   Counterexample: `S(SSS)SSSSS` (9 leaves) terminates but opens one origin 4 times (E4).
2. **Small-context congruence (contexts ≤ 5 S's)** gives non-well-defined products (E5); contexts with
   6 S's are needed before the HN congruence stabilises at 35 classes.
3. **Naive size induction for C1 converse**: minimal counterexample t = t1 t2 with hnf(t1) = S a b
   reduces to a t2 (b t2), which is not smaller — size induction alone cannot work; a different
   well-founded measure or a semantic (realizability) argument is required.
4. **Regular-Böhm-tree non-universality route**: refuted experimentally by R6 (non-regular BTs).
5. **Proving C1 as a new theorem** — superseded: C1 is BEKW Question 10 (our model is isomorphic to their
   Fig. 14) and decidability of head normalisation is Padovani's theorem (Satellite Ch. 7). Kept only as
   verification (Theorem B).
6. **Two-counter races for Böhm-tree finiteness via wrapper families** (E10): no comparison pattern in 4,554
   exact grids. Heuristic obstruction ("single-counter principle", NOT proved): the head machine only forms
   `b·c` with b before c; a W-style decrement `W_m Y → S Y (W_{m-1}Y)` destroys the left value and carries Y
   unchanged; the base gadget (K) can only copy/increment the surviving value (`K Y ⇒ … ⇒ Y (N_1 Y)`).
   A comparison needs two values preserved across rounds; none of the tested gadgets does this.
7. **Program-with-registers counter machines** (overnight, obligation 3): impossible in the S-world by Lemma 8
   (data conservation) and Lemma 9 — code cannot hold two data nor write into data while two data are live;
   transfer layers `S Y1 Y2 x` always inspect their predecessor (Corollary H1, all sizes).
8. **Word dynamics / tag-system passes:** no 2-letter alphabet (gadgets ≤ 5 leaves) closed under the Böhm-tree
   step (E14); structurally, new symbols can only be prepended, and end-to-front rotations duplicate the moved
   element (Lemma 9) — no junk-free queue found.
9. **Finite model for Böhm-tree finiteness by closure** (E15): contexts ≤ 6 and ≤ 7 give closed tables that are not
   S-models (70% / 22% identity violations).
10. **H2 hunt (bounded):** parity along countdowns (none; memoryless), FRACTRAN-style single-datum arithmetic
   (no modular tests), CPS two-counter designs (Theorem J: writes are global, ≤ 1 per step), tag-system passes
   (Prop. M under U-tail/U-acc; exact search 0/5,832). Remaining open: shape-encoded CA-like propagation and
   non-head strategies.
11. **Full-read passes, small gadgets (E18–E19):** no gadget ≤ 5 leaves deletes an unbounded segment after a marker
   (0/11,638) or doubles every symbol of a word in one pass (0). The full-read regime is not excluded by any theorem
   (Lemma 11 below shows it is forced whenever ≥ 3 unbounded blocks are present); only small gadgets are excluded.
12. **Novelty of Theorem C (non-regular Böhm trees):** withdrawn — BEKW §2 (Zachos term `STT(STT)`, Fig. 10) already
   exhibits a Böhm tree with infinitely many distinct subtrees `S Z_n` (E20). Theorem C remains a proved example.
13. **Class-level proof of C6 completeness:** the joint class (P39 × M35) of a term does not determine the joint classes of its
   hnf components (terms ≤ 11 leaves: 71 of 104 classes ambiguous; e.g. a ⊥_P class has hnfs with components of the same
   class). So no finite "Böhm-tree automaton" on these classes exists; completeness needs a dynamical well-foundedness
   argument (code/jointhnf.py).
14. **Ranking-function certificate for Q10 (BEKW's semantic-labelling suggestion):** size-weighted potentials
   Φ = Σ W(labels)·|e_i| with labels (class, below-context) or (above-prefix, class, below-context) are infeasible for all
   terms (LP, code/q10_lp*.py) although feasible on all actual runs ≤ 11 leaves — duplication chains defeat finite labels.
15. **Distinct head origins along leftmost paths** (pigeonhole bound): false (S(S(SS))SS repeats an origin at depth 3).
16. **Linear fast-or-never for leftmost paths (C11):** refuted — SSS(SS^{(k)}(SSS))SS has finite leftmost paths of length
   k² + 3k + 3.
17. **Rightmost path as a pure pushdown on the last argument:** the head machine only wraps the last list element, which
   suggested a pushdown process; but along rightmost paths the original last argument is read in most cases (1,358 of 2,002
   terms with ≥ 3 arguments at 10 leaves), via the clean copy that rises when it is the third element.
18. **Engine lemma for Q10** (infinite head runs expose a small hnf-free kernel as a top prefix): 686 of 892 ⊥-class terms
   (8–10 leaves) hit a kernel of ≤ 10 leaves within 150 steps, but 206 do not (e.g. S(SS)S(SS)SS); kernels are diverse —
   divergence is often non-local (code/engine_lemma.py).
19. **Labelled RPO for Q10** (head reduction as a marked-spine TRS, labels = M35 class pairs of spine nodes): the core
   precedence constraints (s·x·y, z) ≻ (x·z, y·z), (s·x·y, z) ≻ (x, z) over non-⊥ redexes have a self-loop (717 label
   pairs, 2,629 edges), so no well-founded precedence exists; equal labels force argument comparisons that fail on the
   duplicated variable. Together with items 14–16: the standard automatic-termination toolbox (semantic labelling with
   linear potentials or RPO) does not certify Q10 with M35 labels — consistent with BEKW leaving it open.
20. **Finite non-idempotent type certificates for Q10** (Lemma 14 soundness + a finite type set Θ, checked on the magma
   M35 × P(Θ)): impossible for every finite Θ (Proposition T: left combs S^k need head-S types with k − 1 arrows). The
   repair search fails exactly on classes {12, 21, 24, 26, 28, 29, 31}, the same cyclic core where items 14–19 failed;
   the needed types grow in depth with a shared tail. What survives: Lemma 14 (typing ⟺ head normalisation, with an
   elementary weight argument valid for recursive types) — a certificate would need schematic (tail-polymorphic) types.
21. **Simple measures for the leftmost-path finite half** (E36): multiset of provenance pieces (per step or between
   size-increasing nodes), descent of the node's base occurrence, node size between size-increasing nodes — each fails on
   real flag-0 walks (often the walk balloons for one step and collapses, or ends in ⊥ right after). Infinite paths are
   self-reloading counters, finite ones count down without reloading: a proof must show reloads stop (size-change style),
   not that a single quantity decreases.
22. **Attempt 1 at the leftmost-path finite half — exact symbolic size-change abstraction** (code/sct_leftmost.py): head
   machine on configurations of slot parameters with joint L36 × M35 classes, composites, and lazy spine-suffix parameters
   (exact class bookkeeping via the S-identity; opening/expansion strictly decreasing), Lee–Jones–Ben-Amram test on cycles
   through descend steps inside {(14,28),(14,26)}. Infeasible: the joint model is already the coarsest congruence that
   separates the component classes and ⊥ (69 blocks, no quotient); with composites of depth ≤ 2 the exploration exceeds
   200,000 states without closing; with depth ≤ 1 it closes (295,868 states, 726,000 transitions, 5,114 descends) but the
   closure exceeds 3,000,000 graphs, and depth 1 provably cuts the countdown thread ((N_{i−1}·N_k)·S is a depth-2
   composite). Lesson: class-exact micro-step symbolic execution is too fine; peel runs must be summarised in closed form.
23. **Universality attempt U (prize directive, 2026-10-25):** programmable counter machines on leftmost Böhm-tree walks
   built from nests W^n(B) (the full re-execution regime left open by Theorem O). Exact symbolic search (code/nestwalk.py)
   finds only countdowns and the single reload program (i, k) ↦ (k, k+1); no two-counter-with-zero-test family in the
   searched space. Not an impossibility proof.
24. **Universality ladder rung (1), round 1 (agent U, 2026-10-25/26):** a loop inside one infinite head run whose pass does
   A−− and B++ with a zero test re-entering the loop. (a) Counters carried as arguments of the sawtooth's countdown frame:
   blocked by the frame lemma (the carried counter cannot change during the countdown; it is written only by the closed
   base at A = 0, once per outer cycle). (b) Counters on the tape, Φ style: a clean B++ behind a live control needs fuel (a
   closed constant directly below a datum); Φ spends fuel built into its closed program and cannot rebuild it. Bounded
   symbolic searches (324 + 4,347 + 497 families): no A−−/B++ pass. NOT an impossibility proof: fuel can multiply once
   present (E40), and entangled designs (B holds A) are untested — both reopened in round 2.
25. **Universality ladder rung (1), round 2 (agent U, 2026-10-26):** fuel-splitting designs (A carrying 0–2 fuel constants, general A contexts ≤ 4 leaves × fuel lists × tapes, target-holds-fuel tapes, same-family contexts ≤ 6 leaves), entangled node templates and Fibonacci self-compound reload sources. Only three A−−/B++ passes exist, all with fuel in A's own layer, and the reload from B is excluded by Theorem U* (at A = 0 the list is F1/F2 w.r.t. B). Not an impossibility proof: B absorbing closed constants from below during the transfer and entangled tape designs remain untested.
26. **Infinite pump re-entry (agent U round 3, 2026-10-26):** the pump loop (PROOF.md) runs k rounds and stops because each spill re-entry takes the next target from the current target's head spine (placement lemma + G1: a finite descent). Reload of the target base at k = 0 by an outer counter or by the base's code: none found in the bounded searches. Needs a fresh-head generator between target and supply.
27. **Reverse transfer and reload with a fixed control (agent U round 4, 2026-10-26):** every layer shape tried (S S x S, S S x (SS), S(S x)S; write + stale execution) destroys the counter structure, and the write-pass theorem shows why: the stale copy left above a deeper value can never shrink back to a fixed control (leaf monotonicity). A sawtooth generator can ride along the pump exactly but is never promoted to the next target.
28. **Full re-execution transfers (agent U round 5, 2026-10-26):** sawtooth variants with a third counter in the fuel
   slot, a second counter family, three counter slots (reload bases ≤ 8 leaves) and controls F[N_k] (≤ 5 leaves). The only
   loops are countdown + reload of one counter; third counters are re-executed but restored, kept, or overwritten by a
   copy; no unit ever moves between two counters. Bounded, not an impossibility proof.
29. **Reload loop + transfer gadget (agent U round 6, 2026-10-26, at the user's request):** sawtooth + tape counter (every
   tape write is junk·data), head-style countdown inside the sawtooth frame (exact transfer pass A−−/C += r, but at A = 0
   the supply sits in front of B and no base ≤ 8 leaves re-enters a round), pump + sawtooth (reverse transfer excluded by
   the write-pass theorem). No forever-looping counter program with transfers. Bounded searches + traces; the obstruction
   'supply in front of B' is argued, not proved.

30. **Numeral loops with an accumulator (2026-10-26, main agent).** Idea: iterate a loop body with S-numerals
    (Theorem N) and let each iteration transform an accumulator kept just below the loop continuation. Result: among all
    bodies ≤ 9 leaves only the identity body SS returns to the loop with an accumulator built from A and S
    (code/body_search.py); extended to all bodies ≤ 12 leaves (≈ 280,000): still only SS. With the general return
    protocol (control returns as X·Z·w_1…, the next accumulator being w_1) all bodies ≤ 11 leaves: 4,367 return to the
    loop, none with a transformed accumulator over A and S, none even over A, J and S (code/body_search2.py).
    Calls never touch their tape, so iterating a call only spends time. Lesson: data must live
    in the code that the driver rewrites (as in the counters), not on the tape below a loop.
31. **Changing the counting base from cycle to cycle (2026-10-26, main agent).** Idea: start a gadget driver with a
    foreign gadget, or give levels a word of gadgets, so that the driver writes data-chosen digits. Result: static words
    of gadgets are fine (every level is a call, per-letter multipliers), but a driver writes a foreign gadget once and then
    only the base's gadget (level words 3^k·4·3, …): the gadget of each new level is copied from V = SS·X in the return
    values, which the base fixes. A data-dependent driver would need return values that vary with the data.
32. **Data through return values (2026-10-26, main agent).** Idea: use a base whose return depends on the argument y
    (SS returns [Z, y·Z]) so that data flows into the return values and from there into the next level. Result: gadget
    levels over SS return, from level 1 on, the fixed top [Z, S(SS)(SS)·Z, Z(SSZ)(SS(S(SS)(SS))Z), …] — a function of
    Z = x·y alone; y·Z only sinks below as junk (code/ss_returns.py). In every scheme found (BC, TC, K, SS-based) the
    return values depend only on Z, so a call passes data to its continuation only through Z itself.
29. **Size-change termination over finite state abstractions of leftmost walks (main agent, 2026-10-27; E109,
   E112, E113).** Size arcs between all parameter slots fix the composite obstacle of item 22. With the unbounded
   fine state (node class plus the classes of all arguments), the empirical closure has no bad loop for every walk
   from terms ≤ 11 leaves. Every FINITE state abstraction tried fails:
   * node class only: 315 bad loops at ≤ 9 leaves;
   * class + number of arguments: 28; + first/last argument classes: 10; with both: 6;
   * end windows of width 2 or 3: pass at ≤ 10 leaves, then fail at ≤ 11 leaves (4 bad loops) and on random
     12–22-leaf terms (68);
   * the pushdown abstraction without sizes: countdown self-loops (E112).

   Lesson: the information that bounds reloads in flag-0 classes is not in any bounded window of class data. A proof
   needs a structured infinite-state abstraction (e.g. the v-stack of Theorem Q10's chains, with sizes) or a
   different idea.
30. **Opaque bottoms for the leftmost-path finite half (main agent, 2026-10-27; E114).** The generalised Lemma P (any two
   bottom terms; a stop at an atom-headed front counts) is a correct sufficient criterion, but with atom bottoms it fails
   on 5 of the 171 component terms with 8 leaves: their paths are finite, yet the run continues into S-headed code and
   grows without bound. The leftmost half needs a well-foundedness argument for the pushdown-with-reading dynamics of the
   tail chains (E112–E114), not a reduction to head normalisation with extra arguments.
31. **Conjecture R3 for all ordered data (non-universality agents, 2026-10-27).** "After an innermost-dirty transfer
   the next phase cannot transfer" is REFUTED for ordered data with two occurrences of the predecessor
   (D = S(Sp)(S(S(S(SS)(SS)p))), lean/AgentR3F.lean `r3_cx_*`). The chain bound survives because data after the first
   transfer have one occurrence; R3 for one occurrence is open (PROOF.md, "Chain bound in the generic phase model").
