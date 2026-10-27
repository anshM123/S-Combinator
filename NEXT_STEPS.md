# NEXT STEPS (resume here)

## Newest of all (2026-10-26, evening: UR-C in Lean, descents) — read first
* DONE (E108): Theorem UR-C machine-checked (lean/URCore.lean: `walk_out`, `st_ind`, `ur_classification`,
  `ur_counter`; code/lean_check.py → LEAN OK, 19 theorems).
* DONE (E108): CORRECTION. One-redex evolutions can descend into arguments for ever. UR-R/UR-C cover head-unique runs
  only; R57/R67 are corrected. Theorem DK (descending K-counter, base K = S(SS)(SS)) is PROVED. All 140
  forever-descending one-redex terms ≤ 14 leaves enter it (code/descent_runs.py, descent_classify.py,
  descent_k_proof.py).
* NOVELTY (E108): Theorem DK = the Zachos term's known mechanism (BEKW §2, our E20, our Theorem C). Waldmann's "Nimm
  Zwei" (1997) characterizes all one-redex-forever terms, so the one-redex work is very likely not new. Only the Lean
  formalisation and our corrections are ours. Deprioritised.
* PRIZE DIRECTION (user, 2026-10-26 evening: "aim for the money"). Wolfram's announcement (re-read): a disproof must
  show that all evolutions, even infinite ones, have "only a finite, or essentially finite, number of distinct forms",
  or give "jump-ahead" code. A proof must emulate a universal system with a non-universal encoder and decoder (any
  evaluation order, or multiway). Literature check: no solution claimed since 2022 except Vatan (K not S-definable;
  known, does not settle it).
  Disproof chain (PRIZE_ASSESSMENT map): (2) termination halves of the finite models (C6 = BEKW Q5, C8, leftmost and
  rightmost paths); (3) effective R″ for all leftmost-outermost runs; (4) other orders; (d) definitional argument.
  ACTIVE TARGET: the leftmost-path finite half (bad SCC {(14,28),(14,26)} of L36 × M35, mechanism = nested SS(·) counter
  with base B = S(SS)(SS)) by size-change termination over MACRO-steps. Summarise each peel run (countdown of an
  SS(·) nest) in closed form, as FAILED_APPROACHES 22 concluded; then the Lee–Jones–Ben-Amram closure on macro-step
  graphs restricted to the bad SCC. If it works, port it to C6 (17-class SCC) and C8.
  PROGRESS (E109): with SIZE arcs between all slots the empirical size-change closure has 0 bad loops for every walk
  from terms ≤ 11 leaves, and the whole node shrinks in every idempotent loop. Remaining: a finite abstraction plus
  symbolic completeness of the computed step (tail-chain summary). Subterm arcs fail on composites.
  REFINED PLAN (2026-10-27): a PUSHDOWN abstraction instead of fine states. By Q10's tail-chain equations, a computed
  leftmost step from u = S e1…em ends at S v_k (q_k v_k), so the child is v_k = q_{k−1}·(q_{k−2}·(…(q_0·e_m))), a
  right comb of chain values over the node's last argument. The next computed step has prefix q_{k−1} and last
  argument v_{k−1}. A chain of length 0 drops to v_{k−1}; a longer chain pushes new composites. So leftmost walks are a
  pushdown process on the v-stack, which refills may read when they open v_i in H(S x y v_i). Abstract the stack
  symbols by joint classes and the chains by Q10's graph G, then decide 'no infinite abstract run inside flag-0
  classes' by pushdown saturation (Bouajjani–Esparza–Maler). If sound and successful, this proves the leftmost half.
  The same idea may extend to C6/C8 and to head runs: a route to a C5-type theorem.
  The construction side is covered by the subagent (agent_work/LOG.md: Lemmas OC, NC, numeral inertness, no Church
  transfers ≤ 11 leaves).
* Later / low value: the descending one-redex class at every size, and the Lean Observation.
* DONE (E111): construction agent phase 3. OTD, FH, SL and canonical_innermost are Lean-checked (lean/AgentOTD/SL/CANON.lean,
  in verify_all). Open: phase 3 for MULTI-LEVEL data (the replay relation), then the conjecture 're-execution is call-like'
  ⇒ R″_PUP.
* DONE (E113, FAILED_APPROACHES 29): no FINITE state abstraction gives a size-change proof of the leftmost half; windows
  that pass at ≤ 10 leaves fail at 11 and on random 12–22-leaf terms. Needs a structured infinite-state abstraction or a new idea.
* DONE (E112): pushdown abstraction of leftmost walks without sizes has spurious countdown self-loops (584 SCCs at
  stack height 1). A proof must combine classes with size information.
* DONE (E110): the construction subagent finished. No construction; obstruction theorems OT/RC/OC are Lean-checked
  (lean/AgentOT.lean, AgentOC.lean, in verify_all) and NC is a hand proof. Its next steps: extend OT to dirty wrappers
  and duplicating writes, or design comb-parity re-execution rounds.
* (was) RUNNING (started at the user's request, 2026-10-26 evening): a background subagent works on the constructive
  direction (data-dependent control, 2-counter simulation, or a provably non-R″_PUP run), writing only under
  agent_work/ with a log in agent_work/LOG.md. Read its final report and check its claims before recording anything.

## Newer (2026-10-26, night: parallel evaluation)
* DONE (E95–E98): parallel (ReplaceAll) evolution has an exact lazy machine (Lemma LZ, code/lazy_par.py). Theorem PL
  is the first exact parallel run that differs from its head run. Theorem LP-par (code/par_loop_prover.py values,
  code/par_loop_prover2.py lazy representation, code/par_loop_prover3.py evolving combs) certifies **86 of the 150
  census-sample parallel runs** (comb 21/22, loop 35/63, counter-type 30/65; E100). Every certificate is checked against 400,000 concrete passes (code/par_cert_check.py).
  verify_all has checks for LZ, PL and LP-par.
* DONE (E99): unique-redex terms classified up to 17 leaves. Theorems UR-Φ and UR-Φ-II generalise Theorem UR to any base with a symbolic base lemma, and all 2,087 terms ≤ 17 leaves with a unique redex for 3,000 steps are proved unique-redex for ever, linear counters in every order (code/ur_phi_proof.py). NEXT here: the classification for every size — show that every unique-redex-forever run reaches a Φ-state whose walk ends at a base with a base lemma (or find a counterexample). The data say every base contains B = S(SSS)S, and B's role (B → [A, S] → [S, S] → Φ) is the natural starting point. Data for it: code/ur_bases.py lists the 13 base return patterns up to 13
  leaves (E99); bases are always S p or S p S (the first step must keep the second element of spine ≤ 1).
* DONE (E99): randomised differential tests of the lazy machine and the canonical aging rule (code/lazy_par_fuzz.py).
* DONE (E107): Theorem UR-R's core machine-checked in Lean 4 (lean/URCore.lean; code/lean_check.py). DONE (E108): Theorem UR-C formalised too. Still open: the Observation linking `urForever` to "the head redex is the only redex at every step".
* NEXT (E105): thin runs (second element spine ≤ 1, elements may contain redexes): 118 beyond unique-redex at 13–15 leaves, all certified loop runs; 22 alternate Φ-rounds with B-rounds [B, S B, d]. Extend Lemma R′ / UR-R / UR-C to type-k steps (k ≥ 3: registers reset to (a_2, a_3), pushes a_4..a_k, v, u·v) to get a class theorem for thin head runs.
* DONE (E101): Theorem UR-R — every size: after ≤ 3 rounds every unique-redex round is a Φ-round, Φ-elements end in B, A, S, c′ = S c or S z (S^{m−1}(S c)), and the run is a deterministic map Ψ on c. NEXT: classify Ψ's orbits (E101 notes: pointer z of Ψ(c) is self → type II; inner(X) → type-A alternation; inherited → strictly older, terminates). DONE (E103): Theorem UR-C is now a full hand proof (transition rules T0/T1/T2, the death case, inheritance shrinks the pointer, then type A or II for ever), with every rule machine-checked on all real runs and ≈ 1.76M sampled transitions. **Every head-unique S-term is a linear counter in every evaluation order, at every size.** (CORRECTED E108: this first said "every unique-redex S-term ... the class is closed". Descending one-redex evolutions are a separate class, see the newest section.) What would extend it: terms with a *bounded* number of redexes, or the multiway/parallel case for non-unique-redex terms (gap 4 proper).
* Sharper form of the all-sizes unique-redex question (Lemma R′, the round machine): a round's successor is a Φ-round iff its last push is S·v_final, which happens when the walk ends with two type-2 steps with t = S — the B = S A S ending. Show that a unique-redex-forever run eventually ends every round this way. Then reduce the steady state to the finitely many return patterns its bases can have (code/ur_bases.py), and show each pattern either breaks uniqueness or gives a counter. Lemma R′ makes this a finite-register question per round.
* DONE (E100): comb families whose layers keep evolving — loops re-checked with the loop variable as a general atom,
  and a settle check that never unfolds tokens (the earlier 'nested pending passes force the whole comb' diagnosis
  was wrong; the cascade was the prover's own settle check). Remaining 64: 40 timeouts, 17 token-unfolding
  failures, 4 without comb pattern, 3 without growing-loop cycle.
* OPEN: a parallel version of the call prover (60 counter-type parallel runs uncertified; E59: levels decay while they
  wait). Same engine swap as LP-par, but the call lemma needs return forms under aging.
* Caveat: per-term parallel certificates do not close gap 4. A general theorem would need R″_PUP for the nested
  evolutions too.

## Newest (2026-10-26, late evening) — read first
* DONE: every counter-type run of the 12-leaf census is proved exact (call prover 147 + Theorems CD, CD2 ×2, CD3, NS —
  E88–E93), as are the 150-term census sample and all 850 random-hunt endpoints (13–640 leaves). Per-term certificates only.
* What would move the prize question now is not more coverage but a general argument: R″_PUP for ALL terms (the
  certified mechanisms — calls, loops, nested loops, chain/frame recursions — all share a 'finite symbolic certificate'
  shape; a proof that every head run has such a certificate is the open core), or a theory for other evaluation orders.

## Latest of all (2026-10-26, evening) — read first
* Random hunts are complete at every size tried: 850 of 850 endpoints proved (13–640 leaves; E68, E72–E76, E81–E87).
  Prover fixes found on the way: opcode-encoding bug (E83), two-block loop cycles via a marker-based cycle finder (E85),
  scheme inference tolerant of a misdetected last level (E82), template-driver fallback (E81). Large terms' endpoints are
  almost all loop runs; a third square run (444 leaves) is also non-morphic (Theorem NM extended, E87).
* Only 1 run anywhere is unproved: the 'no scheme' counter SSS(S(S(SS)(SS)(SS)))S of the 12-leaf census (E90: Theorem CD3
  proved the last countdown S(SS)S(S(S(S(SSS))S))S).
  Its call structure is known (E91): family members are tail calls down to a base member L_{g,0} = S S (S S D)(S T_{g−1})
  whose call returns R_g(Y) = [Y, S T_{g−1} Y, S S (S C)(S S (S S D)(S C))] (C = chain of T_{g−1}'s layers + T_{g−1}, ending
  in Y). Remaining: lemmas for the base call's walk over T_{g−1}'s chain, and the driver over the tops. DONE (E89, Theorem CD2): the two growing-opcode countdowns S(SS)S(S(S(SS(SS))S))S, S(SS)S(S(S(SSSS)S))S.
  DONE (E88, Theorem CD): the bounded countdown counter S(SS)S(S(S(SSS)(SS)))S, by hand-found chain
  structure + symbolic lemmas (code/countdown_proof.py) — the same method (named trace → closed form for the heads →
  walk/end/open lemmas) worked again for CD2; try it on the last two. Closed forms already found (EXPERIMENTS E88 note):
  growing-opcode countdown — level family a_{k+1} = S S (S a_k)(S (S a_k)), b_k = S (S a_k), widest element
  E_m = S a_{m−1} b_{m−1} a_{m+1} f_m ⋯ f_0 with self-referential frames f_k = S a_k b_k (prefix of E_m up to f_{k+1});
  'no scheme' counter — chain tops through all earlier tops with fixed outer layers Q_1, Q_2.
  Countdown structure (named trace, bounded-opcode run S(SS)S(S(S(SSS)(SS)))S): every epoch starts with [X_m, S X_m,
  S S X_m, …] where X_m = S Y_m and Y_m chains through ALL earlier epochs' heads, S S X_k (S S X_{k+1} (… )) — a list of all
  previous levels inside each new level. A prover needs symbolic sequences of levels (vector/sequence level schemes).

## Latest (2026-10-26, end of the overnight run: NM, UR, innermost, RESUME) — read first
* DONE: Theorem NM (PROOF.md) — the two square runs have non-morphic opcode/window words (Lemma S + certified words from
  code/nest_words.py). Use R″_PUP everywhere from now on; morphic R″ is false.
* DONE: Theorem UR — t_0 = S(SSS)S(S(SSS)S) has a unique redex for ever (all orders agree). Unique-redex terms up to 13
  leaves (2, 3, 10, 26 for 10–13 leaves) all look like the same linear counter. Open: is every unique-redex run a linear
  counter (or at least PUP)? The dynamics is the head machine on normal forms with the second element always S or S z
  (opcodes ≤ 2; rules [S,S,c] → [c,Sc]; [S p,b,c] → [p,c,b·c] with c ∈ {S, S z}; [S p q,b,c] → [p,q,c,b·c] with q ∈ {S, S z})
  — a small closed system; a full classification would settle a whole class for every evaluation order at once.
* NEW AREA: leftmost-innermost evolution (PROOF.md, last sections; code/li_explore.py, li_path.py, cbv_robust.py). Facts:
  descent-or-fixed-depth dichotomy; descending runs freeze the term from the outside (bounded-prefix detectors decidable).
  Open: which terms descend; structure of the frozen spine (S(SSS)S(SSS): always the third argument, nested-loop sibling
  sizes; binary-counter term: exponentially growing normal forms); fixed-depth case = head runs whose first three elements
  stay normal (only one found among 602 runs besides the unique-redex ones).
* DONE: RESUME hardening (E78): counters 147/152, sample 150/150 unchanged. DONE (E81): template-driver fallback in the
  call prover proves the E76 binary counter (40–80 hunt now 99/100); root call-by-value census (1, 13, 40 fixed-depth
  terms at 9, 10, 11 leaves). DONE (E83): opcode-encoding bug (opcodes ≥ 10 misaligned cycle starts) fixed in the loop,
  nested and comb provers; the E76 linear loop is proved (40–80 hunt 100/100). Open small items now: the 12-leaf
  'no scheme' counter (level-dependent return forms) and the four countdown counters — the only unproved runs left in
  every census and hunt. DONE (E82): the E73 base-3 call run (scheme inference now drops a misdetected last level);
  25–40 hunt 150/150. Design idea for the five left (from E83's measurements: each new level element = a comb of
  length ~m around pieces of the previous level): *vector level schemes* — several level families advanced together,
  L^i_{k+1} = F_i[L^1_k, …, L^r_k] (e.g. a comb family C_{k+1} = G[C_k] and L_{k+1} = F[L_k, C_k]); the call prover's
  engine would unfold tokens ('L', i, d) by F_i, and the inference would have to find the r families from the concrete
  run. Not started.
* Still open from before: countdown runs (one with bounded opcodes, three with opcodes growing to 46–51 in 200,000 steps;
  frames walked by a loop with a decreasing count — needs nested
  graded segments; the inner loop count is the outer loop's own variable, so the nested prover needs a second symbolic
  parameter; the epoch-start elements are rebuilt each epoch, sizes obeying X_{m+1} = 3X_m − X_{m−1} + 3, i.e. growth
  by φ² — a coupled two-sequence recursion), the 'no scheme' counter, R″_PUP in general, parallel order (nested evolutions).

## Latest (2026-10-26, loop prover + multiway topology) — read first
* DONE: Theorem LP / code/loop_prover.py (PROOF.md 'Loop runs proved exactly'); census sample now 150/150 non-counter
  endpoints proved exact (E67); counters 145/152 with strong numerical tests (E66); 100/100 endpoints of random
  13–16-leaf terms (E68). Proposition MW (PROOF.md, multiway topology): potential (size, −leaf depth), acyclicity,
  decidable reachability, Gross–Knuth cofinality for reduction-closed detectors, no mirroring of nondeterminism.
* The census sample is fully proved (E67). Unproved: 7 counters (countdown/cubic nested loops, 2 'resume unsafe', 1 'no
  scheme') — see the next bullet. Also: the two
  unbounded-opcode runs (cubic schedule, nested loops) and 8 unproved counters.
* LATEST (E74–E76): nested-loop prover proves the square runs; hunts at 40–80 leaves 98/100; parallel evaluation keeps
  infinite evolutions waiting in the list (301/302 runs) — gap (4) needs a theory of nested evolutions. Open small items:
  call-prover driver for the E76 binary counter; pattern inference for the E76 linear loop; the E73 base-3 call run.
* NEW (E72, E73, PROOF.md 'Weakening the bridge'): UB only needs window words that are effectively profinitely ultimately
  periodic (Carton–Thomas); square nested runs exist at 25–40 leaves (round m = m identical blocks X Q^{m+c} Y) and may
  not be morphic. DONE: code/nest_prover.py (Theorem NL) proves both square runs (E74). Next: (1) countdown runs — traced (2026-10-26): the stack holds a list of
  pending frames F_k·Y·Z; each iteration pops the top frame as the next front, and its inner loop of k blocks walks the
  remaining frames and rebuilds each (new second component, new shared third component Z). Needed: loops that consume
  and rebuild stack segments (block lemma over 'first segment element → rebuilt element'), not just a second variable;
  (1b) settle morphicity of square words via Smith's zigzag characterization (PROOF.md, Theorem NL); (2) decide whether ∏_m (a^m b)^m is morphic (if not,
  morphic R″ is refuted by E73's runs once their structure is proved); (3) the base-3 call run of E73 (family search).
* DONE (E69/E70): whole-list certificates (every window size k) for every proved run — Corollary LP′ (loop pushes as graded
  segments) and Corollary CA′ (call residues as a recursive list grammar, RESUME remainders barrier-checked).
* Remaining census mechanism with no prover: the countdown / unbounded-opcode runs (S(SS)S(S(S(S(SSS))S))S,
  S(SS)S(S(S(SS(SS))S))S, S(SS)S(S(S(SSSS)S))S, S(SS)S(S(S(SSS)(SS)))S): epoch m reads (m−1) m (m−2) m ⋯ m 4 m m m in
  the large opcodes; fronts are lists of ~m entries built from earlier fronts' entries (sizes doubling). Needed: graded
  list segments on the stack (symbolic length, entries F^i(x)) and nested induction (block lemmas proved with inner
  loop macros, polynomial step counts). The two 'resume pattern unsafe' counters are PROVED now (barrier criterion, E71); the 'no scheme' counter
  SSS(S(S(SS)(SS)(SS)))S is a call recursion whose return form carries a comb growing with the level (needs parametric
  return forms). The call prover is very slow on some loop-type terms
  (> 10 min on S(SSSSS)S(SS)S) — add a global time budget so the loop prover is reached sooner.
* The general statement (R″ for every term) is still open; per-term certificates cannot give it. Ideas for a general
  route: show every infinite head run decomposes into calls, loops and list walks (the three certified mechanisms) — no
  candidate argument yet.

## Latest (2026-10-26, later: binary counter solved, call algebra, rules) — read first
* R″ for all head runs ≤ 12 leaves (E62, E63): counters 144/152 proved automatically; non-counter endpoints ~11% proved
  (sample) — after the linear-scheme fix (E63) ≈ 39% of non-counter endpoints are proved. Next: a parametric iteration
  lemma for the comb runs (75/150 have no call family). They are single counters whose opcode words are exactly
  D·B^m·D·B^{m+1}⋯ (E63 notes; certified on windows for four examples) — needed: an inner-loop lemma (one block B per
  element of a growing structure) plus driver derivation, analogous to the call machinery.
* Re-verify everything new with `python code/verify_all.py` (run from code/; 31/31 PASS on 2026-10-26, about two minutes).
* DONE: Theorem BC (PROOF.md 'The binary counter, exact'): exact driver, t_k = 144·2^k − 48k − 104, morphic opcode word;
  all five known binary counters are the same machine. Theorem CA (PROOF.md 'Call algebra'): composable S-calls, k-ary
  counters for every k. Rules re-checked (STATUS R34, PRIZE_ASSESSMENT top).
* Because the weak definition lets a universality proof choose the evolution order, the cheapest prize route (if S is
  universal) is a leftmost-outermost construction. Open item 1: a DATA-DEPENDENT DRIVER — a term whose continuation
  builds the next call level from a counter value or a branch (tree calls are data-blind; the binary counter's driver
  builds levels in a fixed way). Pieces available: tree calls (Theorem CA), head-machine booleans (S selects the second
  continuation, SS the first), zero tests (sawtooth), countdown passes (R29). Known obstructions: write-pass theorem,
  Theorem O (Ω(a²) transfers), U*/Corollary W (fuel-free regime).
* Open item 2 (non-universality side, order independence): separate every result into order-independent (Böhm-tree
  properties: invariant under reduction) and leftmost-outermost-only; any disproof must also handle detectors reading
  intermediate states under other orders and the multiway system.
* DONE since: census E56 (148 base-2 ruler runs, only 21 the BC machine; 2 runs with unbounded opcodes), S-numerals
  (Theorem N), ternary counter exact (Theorem TC), counters in every base (Theorem K), order-independence section
  (Theorem T: termination is all-or-nothing and decidable for every order).
* Parallel evaluation (E59): sizes of every small non-normalising term are not linear-recurrent (maximal Berlekamp–Massey
  complexity, generic for 6–9 leaves), so that test does not detect complexity. Since the weak definition lets a
  universality proof choose the order, parallel evaluation still needs its own structure theory (size-sequence tests are
  too coarse: k-regular sequences grow only polynomially, these grow exponentially); next step: describe the evolving tree
  of SSS(SS)S(SS(SS)) per pass (head spine, the recurring datum sizes 70, 100, 157, …), e.g. by tracking which subterms
  are copies of which earlier subterms under the parallel step.
* SUPERSEDED by Proposition CF (R47): control flow (which argument gets control) is invariant under reduction, so no
  clock or timeout can steer control under any order; parallel evaluation differs from leftmost-outermost only in
  intermediate syntax and timing. A universality route via the order must therefore be purely syntactic (detector-side).
* (old) Clock reader = timeout test: a delay term (normal form after exactly D parallel passes) opened at time T shows whether
  T ≥ D. Head-visible delays exist only for D ≤ 5 (≤ 9 leaves); longer ones finish inside S a b, so the reader must open
  arguments. Infinite clocks (e.g. K0) never hand control back and S-terms cannot cycle, so timeouts are the natural
  readable clock. Next: a robust driver (K0-type, R45/BC2) whose cycle opens a delay term created at a known time.
* Clock steering (E59 notes): robust drivers exist (R45), but appended clocks are never read and clocks inside the code
  destroy the counter. Next: design a reader — code that opens the clock at a controlled moment and branches on it —
  inside a robust driver.
* NEW best lead for universality (R43): under parallel evaluation, waiting terms act as clocks (time → data). Try to
  build a data-dependent loop from calls (whose parallel times equal head times, E59) plus clocks whose state at the
  return selects the next branch; and, on the disproof side, note that parallel evaluation needs its own theory.
  Found clocks give only noisy readouts (E59: spines grow ≈ linearly with fluctuations, or freeze at 1–2); first design a
  clock with an exactly predictable readout (e.g. spine length t + c, or a 2-periodic shape) under parallel evaluation.
* Next concrete question (universality side): can a driver change the gadget (the base) from cycle to cycle, or write a
  WORD of different gadgets into the levels, choosing each letter from data carried in the return values? In the K-driver
  the new level's gadget is copied from V = SS·X, which the base re-emits in every call's return values, so the base fixes
  it. A driver that appends data-chosen letters would give tag-system-like dynamics.

## Latest (2026-10-26, binary counters) — read first
* E54: the head run of SSS(SS)S(SS(SS)) (10 leaves) and several larger terms are BINARY COUNTERS (ruler sequence).
  Conjecture R' is refuted; my E47 classification of these terms was wrong. Revised Conjecture R'' (every head run is
  morphic) is open.
* Top open item: derive the exact carry rule of the binary counter symbolically (the digits live inside the new
  elements at each recurrence of [S, S(SS(SS)), S(S(SS)S)(SS(SS)), ...]); then ask whether the carry mechanism can be
  generalised to other finite-state transductions — the only route to universality this project has not excluded.

## Latest (2026-10-26, frontier research by the main agent alone; no more subagent rounds per the user) — read first
* Round 6 (agent U, audited in audit 11): no forever-looping counter program with transfers; best piece = head-style
  countdown pass (A--, supply += r), PROVED for all n (n + 2r + 5 steps). The supply always sits in front of B at the
  zero test (theorem for this family); base S's re-entry is the flat iterator, not a reload.
* Main agent: template-free growth searches (only the sawtooth grows), layer census (supplies never decrease; Lemma SM
  argued), flat comb iterator S.S^n.B.S -> S.S^(n-2).B.S (parity exit), no flat->flat transfer (markers <= 6 leaves).
* SYNTHESIS (PROOF.md, last section): operations O1-O5 found; the two operations universality would need — flat->nest
  rebuild (excluded by the write-pass theorem for fixed controls) and flat->flat transfer (not found) — are missing;
  Proposition MM (PROVED): copy/reset/increment machines with residue/threshold tests are finite-state; Conjecture R':
  head runs only have O1-O5 (would give non-universality for LO + regular detectors, one evaluation order only).
* Lemma SM now PROVED for B tracked by identity (proof in PROOF.md, not independently audited; the term-matching
  wording is FALSE, E51); Lemma NT (strict two-supply form) PROVED likewise.
* Next, if continuing: (1) get Lemma SM and Lemma NT independently audited when subagents are allowed again; (2) look for a flat->nest rebuild whose control carries a
  copy of the value (the only loophole the write-pass theorem leaves); (3) only then attempt R'.

## Roadmap for Conjecture R' (what a proof would need; status of each piece)
1. Episode decomposition of an infinite head run (descend first-child chains to a leaf, then jump to position 3) —
   elementary, not yet written.
2. Iteration lemma: between consecutive front nodes of one counter lineage only that counter and fuel-supplied
   arguments change — the frame lemma (audit 7, fixed form) plus the core-headed hypothesis per template.
3. Reload lemma: at a zero test the base acts with fixed code; one wrap per reload — write-pass theorem (audit 10).
4. Supplies are monotone within rounds — Lemma SM (proved, NOT audited; term-matching wording false).
5. No flat->nest rebuild with fixed control (write-pass theorem) and no transfer into a second supply in the strict form
   (Lemma NT, proved, NOT audited).
6. Closure: operations 2-5 generate copy/reset/increment machines with residue tests — Proposition MM (proved).
THE GAP: step 1 -> 2, i.e. proving that every infinite head run is eventually built from such iterations at all (that
counter lineages and recurring nodes exist). Evidence only: censuses E47/E52-E54, growth searches E48/E53.

## Previous block (2026-10-26, after prover rounds 3-4 and audits 8-9)
* CONVERGENCE: the head-run route and the earlier leftmost-path route (Theorem O) now stop at the SAME frontier — full
  re-execution: a counter can only grow beside a live control if a copy of it is re-read every pass (write-pass theorem,
  audit 10 running; Theorem O for leftmost paths). All unbounded computation would have to happen inside full executions
  of closed terms acting on data ('global rewriting'). No result here constrains that regime; no construction uses it yet.
* Built and audited inside one infinite head run: sawtooth loop; three clean 2-step transfer passes; the pump loop and its
  head-style variant T(k,n) -> T(k-1,n+1) (two counters, clean transfer k -> n, zero tests on both) — every loop found
  either does not transfer or runs finitely many rounds.
* Running: prover round 5 (full re-execution: sawtooth variants with a third counter in the fuel slot); audit 10.
* If a future session continues: (U) try to make a full execution of a word-encoding term X act as a gsm/tag step on the
  data (iterated self-execution); (D) try to show hnf(X d) depends on X through a regular (finite-state) transduction,
  which would bound what full re-execution can compute.

## Previous block (2026-10-26, after audit 7 and prover round 2)
* Audit 7: Theorem U*, Corollary W, sawtooth rules CORRECT; frame lemma CORRECT in a fixed form; 'fuel is never created'
  FALSE when fuel is present (only fuel-free prefixes stay fuel-free). PROOF.md updated with all fixes.
* Prover round 2: only three clean A--/B++ passes exist in the searched space, all with fuel in A's own layer; the loop
  cannot be re-entered because B is fuel-free at A = 0 (Theorem U*). Audit 8 pending for these claims.
* Remaining loopholes for a looping transfer inside one head run: (1) B absorbs closed constants from below it during A's
  countdown (so B is fuel-carrying at A = 0); (2) entangled tape designs whose stale part stays uniformly inert;
  (3) readers for Fibonacci self-compound counters. Disprover target: a sub-target-region lemma (elements below the
  lowest B-element change only by absorption, and grow only when that element is opened) to bound route (1).

## Previous block (2026-10-26, prover vs disprover, round 2)
* Prover (agent U) round 1: rung (1) BLOCKED for two architectures (FAILED_APPROACHES 24; PROVER_LOG.md entries 1-3).
  The sawtooth is an exact loop with a data-driven zero test, but no pass moves a unit from A to B.
* Disprover (main agent): PROVED Theorem U* (the tail-normal invariant survives zero tests, whole infinite run) and
  Corollary W (no clean write into the target while the control has a clean list element). Found that fuel multiplies once
  present (E40), so the prover's 'fuel is never created' only holds with zero fuel.
* Running now: audit 7 (agent aedb7ec9…: sawtooth rules, frame lemma, fuel claims, U*, Corollary W); prover round 2
  (fuel-splitting designs, entangled designs where B holds A, Fibonacci self-compound reload sources). Nothing is promoted
  until audit 7 reports.
* Disprover next: a quantitative fuel law that handles copies (what a write behind a live control consumes, and what
  regenerates it), or a gadget that regenerates fuel per pass (then hand it to the prover).

## Previous block (2026-10-25, prover vs disprover)
* Roles (user's request): research subagent = PROVER (looping transfer program -> Minsky machine inside one infinite
  head run); main agent = DISPROVER; audit-6 agent = independent auditor.
* Disprover's working frame: a head step opens position 1, extends position 2 in place by appending position 3, duplicates
  position 3, and freezes positions >= 4 until they rise. Buried counters change only at positions 1-2 and are re-read only
  through copies made at position 3 — a 'copy-reset' counter structure; target: decidability of regular-pattern
  reachability for every such program (or the exact point where a Minsky machine fits in).

## Previous block (two-route round)
* PROVED and audited: agent U's transfer construction Φ(k, m) — one infinite head run executes P→M, M→Y transfers,
  Y countdown, then loops (data-driven zero tests, straight-line control); Theorem U (with the initial condition F1/F2).
* Audit 6 found that loops ARE possible in a single head run (reloading sawtooth in the probe t z z of the E36 term).
* Universality next step: combine the reload loop with agent U's transfer gadget — a looping counter program with
  transfers inside one head run (the core of a Minsky machine). Non-universality next step: a precise structure theorem
  must account for reload mechanisms; the generation-bound heuristic is false as stated.

## Previous block (infinite-head-run idea)
* New regime identified: infinite head runs (leftmost-outermost evolution of hnf-free terms) — Lemma 9 needs termination,
  so nothing excludes computation there. Data ≤ 10 leaves: only periodic runs and single linear counters (E38).
* Next (pick one): (a) structure theorem 'infinite head runs are finite compositions of linear counters' → decidability
  of regular syntax-sensitive detection along LO for hnf-free terms; (b) engineer a two-counter infinite head run with
  data-driven zero tests (first step to weak universality).

## Previous block (evaluation-order pivot)
* Target fixed (PROOF.md 'Prize target'): weak universality with a regular redex-selection rule, a regular detector and a
  homomorphic encoder; unrestricted (polynomial-time) orders trivialise the question.
* PROVED: Theorem SI — any regular detector that respects convertibility is constant along every reduction path, under
  every evaluation order. So a universal emulation must use a syntax-sensitive detector.
* Attempt U (universality via programmable nest counters on leftmost walks): no construction (FAILED_APPROACHES 23).
* Obstacle (both directions): decidability or undecidability of 'the σ-path of t meets D' for a regular order σ and a
  syntax-sensitive regular detector D. No current technique addresses it; per the directive, no further extended
  auxiliary programme is started without a new idea.

## Previous block (prize-directive round)
* Directive in force: prize-only work; one researcher + at most one auditor; ≤ 3 distinct attempts per obligation, then
  pivot; no papers/outreach/big censuses; checkpoint reports = proved / remaining / credible route.
* Leftmost finite half: attempt 1 (exact micro-step symbolic SCT) FAILED for scale (FAILED_APPROACHES 22).
  Attempt 2 (next, distinct): macro-steps per node with peel runs summarised in closed form (Fibonacci peeling, Lemma 5)
  and SS-nest depths as integer counters, i.e. a counter-system abstraction; termination by linear ranking functions +
  structural decrease. Attempt 3 (if 2 fails): minimal-counterexample size bound (Lemma 13 style) + the existing census.
* Prize assessment (directive): completing the leftmost half only gives decidability of one Böhm-tree path property —
  NOT non-universality. Remaining for a disproof: all decoder-relevant BT properties, the modularity hypothesis of
  Proposition R, and arbitrary evaluation orders / syntactic detectors (Wolfram's weak universality) — the last has no
  current tool. No universality construction exists either.

## Previous block (reload-cycle round)
* Lemma P and Theorem LP1 are now AUDITED (audit 5) and strengthened: outside D2 = {24,26,28,31,34} every leftmost path
  ends at the leaf S; a path ending in ⊥ also makes every t A B diverge, so probes cannot certify it.
* Remaining for the leftmost model: size-change termination of the leftmost walk inside {(14,28),(14,26)}. Infinite paths
  are reloading counters (B N S ↦ N (SS N) S, PROOF.md 'Reload cycles'); single measures fail; targeted search found no
  flag-0 term that reloads forever.
* Next: build the symbolic transition abstraction (slot templates, spine-opening case splits by joint class, size-change
  graphs), run the SCT closure test on the flag-0 component, and send the abstraction to the SAME auditor (audit 5's agent)
  before promoting anything. No large enumerations.

## Previous block (leftmost-path round)
* PROVED this round: **Lemma P** (infinite leftmost path ⇒ t A B has no hnf for all A, B) and **Theorem LP1** (every
  term outside the two-argument-dead M35 classes D2 = {24,26,28,31,34} has a finite leftmost path). Remaining for the
  leftmost model: flag 0 ⇒ finite for 18 flag-0 joint classes inside D2; only {(14,28),(14,26)} resists the coarse graph.
* Infinite leftmost paths are self-reloading SS(·)-counters (E36). Next: a size-change certificate tracking the node's
  spine-argument slots across size-increasing steps (countdown = structural decrease of one slot; show reloads cannot
  recur in flag-0 classes). Alternative: open probe t z z with a model over {S, z} — needs a C oracle (Python learner
  too slow) and a separate argument for the absorbing stuck class σ.

## Previous block (after audit 4)
* **BEKW Question 10 is PROVED** (PROOF.md Theorem Q10; audited). Unconditional now: Props Q, Q′, Q″, Theorem E's E-hn.
* Next obligations, in order:
  1. **Remaining halves via Böhm-tree path certificates:** "flag 0 ⇒ leftmost path finite" (L36; only the joint classes
     (14,28)/(14,26) resist the coarse certificate, code/btpathcert.py left), then R19, C8 (F_fin ⇒ finite), C6
     completeness. Concrete paths in the resisting classes run a nested SS(·) counter (E35): find a measure for it (e.g.
     the nest inside the first component of composite nodes) and add it to the abstract state.
  2. With a path half proved: Proposition R / Corollary R1 becomes unconditional for that path (non-universality for
     modular emulations along it).
  3. Write Theorem Q10 up as a short paper (PAPER_DRAFT.md) — release only with the user's approval.
  4. Conceptual gaps for the prize: the modularity hypothesis of Proposition R; evaluation orders other than head /
     leftmost-outermost (Wolfram's weak universality allows any order).

## Previous "latest" block (after audit 3)
* Question 10 remains the linchpin. Standard termination toolbox exhausted (FAILED_APPROACHES 11–20). New exact tool:
  **Lemma 14** (non-idempotent types ⟺ head normalisation; weight drops by 1 per head step, recursive types allowed).
  **Proposition T:** no *finite* type set certifies Q10; failures sit in classes {12, 21, 24, 26, 28, 29, 31}.
* Next obligations, in order:
  1. **Schematic type certificates:** allow a tail variable ρ in reduction-form S-axioms ([M1 → M2 → ρ] → … → ρ) and in
     the types of terms that pass the rest of the spine through; prove soundness for schemas (instantiate ρ, then
     Lemma 14) and test with `code/nicert.py` whether finitely many schemas close the seven failing classes. Start with
     the left combs S^k (types τ_j, T_j in Prop. T) — they must become one schema.
  2. **C12 (bounded re-opening):** look for a pumping argument "third opening of an application occurrence ⇒
     divergence"; compare opening counts with the multiplicities of canonical derivations (Lemma 14).
  3. **Audit** Lemma 14, Proposition T and C12's statement (not yet independently audited).
  4. Outreach drafts (OUTREACH_DRAFTS.md) and Padovani's chapter: user's decision; nothing sent.

# Earlier plan — after the H2 hunt and the H1 formalisation (Theorem O)

## State in one paragraph
Literature: normalisation regular (Waldmann/CRZ); head normalisation decidable (Padovani); BEKW's 35-state automaton =
our M35; non-regular Böhm trees already in BEKW (Zachos term); BEKW Q5 (productivity regular/decidable?) open. Proved
here (PROOF.md): Lemmas 5–12, Prop. F/G/M, Theorems H, H3, J, N* (per-occurrence), **O**. The bounded H2 hunt (8 targeted
attempts, all exact) found no loophole.

## The picture now (all PROVED unless marked)
* Per Böhm-tree step, ≤ 2 unbounded blocks escape full execution (Lemma 11); with two unread blocks nothing is written
  (Theorem J) and no potential grows along the path (N*).
* Hence (Theorem O): a counter can grow beside a large unread counter only in stretches costing ≥ min(a/2, b/3) − K_0;
  bounded-cost two-counter simulations are impossible; transfers cost Ω(a²).
* Surviving universality designs: **full re-execution** (each growth step re-reads a whole counter, e.g. duplicate it,
  execute one copy, discard the products into the unchosen component), Gödel-style single-counter arithmetic (needs
  modular tests — blocked so far), garbage-stored potential, non-head strategies.

## Master conjecture
**C5** (PROOF.md): Böhm trees of S-terms are higher-order-recursion-scheme trees; **C5′**: their MSO theory is decidable.
Proposition P: C5′ ⇒ no emulation of a universal TM whose halting signal is MSO-definable on Böhm trees (H1 in BT/LO
semantics). The only regime C5 must still tame: full executions of closed terms (CA-like global rewriting).

## Next proof obligations (in order)
1. **Full re-execution regime.** Either construct a "garbage-collected execution" gadget — node `G[⟨a⟩,⟨b⟩]` whose path
   reaches `G'[⟨a⟩,⟨b+1⟩]` after fully executing a copy of ⟨a⟩ — or prove that executing a copy of a counter always
   leaves products in the chosen component (contaminating the checkpoint). Exact symbolic tests first (small G, nests /
   combs / wrappers as counters), no large enumeration.
2. **BEKW Question 5 (productivity) — candidate answer found (E22, Conjecture C6):** P39 agrees with brute force to 19
   leaves. Next: prove C6. (a) soundness: DONE modulo BEKW Q10 (Proposition Q, joint model P39×M35); (b) completeness: CERTIFIED to 19 leaves (E23); general proof needs a well-foundedness argument —
   target Conjecture C7 (⊥ at depth ≤ |t| − 3) or productivity is subterm-closed + the 439 lethal class pairs. Also: compare with Satellite Ch. 7 (novelty). Do not redo the census.
3. **Entangled encodings / garbage contexts:** extend Theorem O (stored potential is spent, never replenished —
   formalise for regular garbage families).
4. **Audit:** DONE for Lemmas 8–12, N*, Theorem O, Proposition Q (audit 1), Theorem P2, Propositions Q′, R (audit 2),
   Lemma 13 and Proposition S (audit 3); repairs applied. Not yet
   independently audited: the learner's models (finite facts), Theorem C, Lemma 14, Proposition T.

## Do NOT redo
Literature search; censuses ≤ 19 leaves; HN congruence; isomorphism; E9–E20; transfer-layer, alphabet, tag, shift,
delete, copy-mode searches; BT-finiteness closures at contexts ≤ 6/7.
