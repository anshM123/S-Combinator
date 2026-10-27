# EXPERIMENTS

Toolkit: `code/sterm.c` (compiled with Lean's bundled clang: `~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanc -O2 -o sterm.exe sterm.c -Wl,--stack,268435456`).
Hash-consed DAG terms; modes `hnf nf bt lo trace enum btenum btprof cong` (see header comment).
Python: `code/origins.py` (origin-tracking head reduction), `code/verify_model.py` (finite-model checker).

## E1 — head/normal-form census, all terms ≤ 14 leaves  (data/enum_n.txt)
Q: how long can head normalization take when it succeeds?
Params: head budget 2·10^4 (n ≤ 11), 10^5 (n = 12..14); nf budget 2·10^4 / 5·10^3.
Columns: rank hnfcode hsteps hnfsize nfcode nfsteps nfsize term.
| n | terms | hnf | no hnf in budget | max hnf steps (term) |
|---|---|---|---|---|
| 7 | 132 | 132 | 0 | 9 |
| 8 | 429 | 414 | 15 | 11 |
| 9 | 1430 | 1294 | 136 | 16 `S(SSS)SSSSS` |
| 10 | 4862 | 4121 | 741 | 15 |
| 11 | 16796 | 13596 | 3200 | 17 |
| 12 | 58786 | 46056 | 12730 | 19 `S(SS)(SSSSSS)SSS` |
| 13 | 208012 | 159040 | 48972 | 21 |
| 14 | 742900 | 557285 | 185615 | 23 `S(SS)(SSSSSSSS)SSS` |
Smallest non-normalizing terms (n=7): `SSS(SS)SS`, `S(SS)SSSS` (both have hnf).
Answer: huge gap — success within ≤ 23 steps, else ≥ 10^5 steps. ⇒ conjecture C2.

## E2 — Böhm-tree depth census (data/bt_n.txt), depth cap 24, per-node head budget 5000
Infinite (≥24) BT depth first at n=8: `SSS(S(SS))(SS)`, `S(SS)S(SS)(SS)`, `S(S(SS))SS(SS)`, `S(S(S(SS))S)SS`.
Counts reaching cap: n=8: 4, n=9: 22, n=10: 70.

## E3 — Böhm-tree profiles (code: `btprof term D K budget`; data/btprof_910.txt)
`S(SS)S(SS)(SS)`: node sizes bounded (≤41), distinct depth-5 signatures stabilise at 19 ⇒ regular-looking.
`SS(SS)(S(S(SS)))(SS)`: max node size 58→130 over depth 4→40 (+12 per 8 levels); distinct depth-K
signatures per level for K=12..20 identical: 29, 39, 50, 60 at depth 12, 18, 24, 30 ⇒ non-regular BT (R6).
Caveat: ⊥ decided by budget 3000 (justified a posteriori by R3/C1 for these sizes — not yet re-checked with M35).

## E4 — opening statistics (code/origins.py, n ≤ 11, budget 400)
Hypothesis "terminating runs open each origin ≤ 2 times": REFUTED (n=9 `S(SSS)SSSSS` opens an origin 4×).
Observed: openings of *created* compounds in terminating runs ≤ 5 (n ≤ 11); diverging runs open some
origin a 3rd time by step ≤ 23.

## E5 — syntactic congruence of HN (code: `cong Nr Nc budget out`)
Representatives: all terms ≤ Nr leaves; contexts: all one-hole contexts ≤ Nc S-leaves; HN decided with budget 400.
| Nr | Nc | classes | product closure | well-definedness violations |
|---|---|---|---|---|
| 7 | 4 | 29 | 261 new | 72/196 |
| 7 | 5 | 32 | 284 new | 44/196 |
| 8 | 5 | 34 | closed | 122/625 |
| 9 | 5 | 34 | closed | 339/2055 |
| 8 | 6 | 35 | closed | 0/625 |
| 9 | 6 | **35** | **closed** | **0/2055** |
Model file: `data/model35_hn.txt` (= cong_9_6.txt). Verified by `python code/verify_model.py data/model35_hn.txt 14 data`:
S-identity violations 0; all hnf shapes in F; ⊥ = class 33 unique & left-absorbing; S generates all 35;
agreement with E1 census for every n ≤ 14 (0 false positives, 0 false negatives).

## E6 — call-tree abstractions for C1 (code/callgraph.py, code/tailgraph.py, code/bigstep.py)
Class-only abstract call graph: 465 nodes, 3 cyclic SCCs through App nodes (one of size 51 around class 12;
tail self-loops App(26,16), App(24,16)). Concrete tail chains in terminating runs have length ≈ |t|−3
(n=12: 9) with repeated abstract states; mechanism = peeling `[S x,q,v] ⇒ [x,v,qv]` with Fibonacci-like
growth of (q,v). Refined (shape-tracking) tail graph: with first components restricted to hnfs only one
(spurious) refill cycle remains; allowing non-hnf first components gives 527,890 refill edges in cycles.
Conclusion: C1 needs symbolic execution with class-annotated variables (not pursued further; C1 is BEKW Q10,
decidability already proved by Padovani).

## E7 — Böhm-tree finiteness congruence (sterm.exe `cong Nr Nc 200 out o1`; oracle: hnf with budget 4|t|+200,
depth cap 400)
| Nr | Nc | classes | new classes in products | inconsistent |
|---|---|---|---|---|
| 7 | 5 | 21 | 16 | 37/196 |
| 8 | 5 | 24 | 5 | 101/625 |
| 8 | 6 | 39 | 18 | 254/625 |
| 9 | 6 | 44 | 14 | 1198/2055 |
| 10 | 6 | 48 | 12 | 4842/6917 |
| 9 | 7 | 45 | 14 | 0/2055 |
(run (10,7) stopped on user request.) Oracle sanity: S(SS)SSSS finite BT (root S(·)(⊥)); S(SS)S(SS)(SS),
SS(SS)(S(S(SS)))(SS), SSS(S(SS))(SS) infinite; stable for caps 100/400/1600.
Two-parameter grid (sterm `grid nS 10 1 400 fam`): templates with nS ≤ 3 extra S's and holes X=fam(j),
Y=fam(k), j,k ≤ 10, fam ∈ {nest, chain}: 0 of 352 templates per family show ≥ 9 distinct rows (no simple
threshold comparison j ≤ k found at this size). Files data/grid_bt_*.txt.

## E8 — literature comparison: M35 vs BEKW Fig. 14 (data/bekw_fig14_table.json)
Table reconstructed from glyph coordinates of `literature/BEKW_dance_of_the_starlings.pdf` p.18 (35 rows × 35
cols, ∞ = state 34). The table is an S-model (0 violations). Unique generator-preserving map M35 → Fig.14:
{0:0,1:1,2:2,3:6,4:3,5:7,6:11,7:14,8:4,9:8,10:12,11:15,12:13,13:16,14:18,15:26,16:5,17:9,18:19,19:27,20:17,
21:20,22:22,23:28,24:24,25:31,26:10,27:21,28:23,29:29,30:30,31:25,32:32,33:∞,34:33} — bijective,
homomorphic on all 1,225 products, acceptance-preserving. **Isomorphic.**

## E9 — exact nest family X(a,b,c) = S S N_a N_b N_c, a,b,c ≤ 12 (data/fam_xabc_bt.txt; oracle BT-finite, cap 400)
By Lemma 5: X(a,b,c) → S F_{b+1} F_{b+2} with F_0 = N_a N_b, F_1 = N_c. Only 12/2197 have infinite BT:
(a,b,c) ∈ {(0,2,1),(0,2,2),(0,3,1),(1,2,1),(1,3,1),(1,4,1),(3,2,1),(3,2,2),(4,2,1),(4,2,2),(5,2,1),(5,2,2)};
all larger parameters give finite BTs (eventually constant). (1,3,1) is the non-regular example; its infinite
BT path (sterm `infpath`) revealed the counter of Theorem C.

## E10 — structured two-parameter families (Böhm-tree finiteness), all exact enumerations of families
* Wrappers V_0=B, V_{m+1}=S U V_m (U,B ≤ 4 leaves) applied to N_k / W_k / same family, both orders, j,k ≤ 12:
  486 grids, 82,134 terms: only 36 non-constant grids, max 3 distinct rows/cols, all eventually constant
  (data/fam2*.txt).
* Two-counter "races": left V^{U,B1}_j applied to right V^{U,B2}_k, U ≤ 4 leaves, B1≠B2 ≤ 5 leaves, j,k ≤ 10:
  4,554 grids, 551,034 terms (55 s): max 3 distinct rows/cols, no threshold/comparison pattern (data/race*.txt).
* Unary contexts ≤ 4 S's, families nest/chain/A^j, j ≤ 40: 0 non-eventually-periodic sequences
  (data/unary_bt_*_4.txt). (Run with ≤ 6 S's stopped: too slow, superseded by targeted families.)

## E11 — wrapper depth saturation (data/depth*.txt; oracle BT-finite, cap 400)
W-family (U=S), bases ≤ 4 leaves, all one-hole contexts ≤ 6 S's, m = 0..8: 11,475 sequences, all constant for
m ≥ 1 except 2 (context `□ N3 N1`, bases S, SS: `1,0,1,1,…` — W_1 recreates Theorem C's counter), all constant
for m ≥ 2. General wrappers U, B ≤ 3 leaves, contexts ≤ 5 S's, m = 0..16: 5,616 sequences, all constant from
m ≤ 2 (no period > 1, no aperiodic pattern). Interleaved two-counter templates (`S X b Y` etc., W-families with
bases ≤ 4 leaves + K, j,k ≤ 9): 1,700 grids, ≤ 2 distinct rows/cols (data/race2*.txt).

## E12 — general pumping families (data/pump*.txt)
t_k = P^k[D], P one-hole context with 1–3 S's, D ≤ 3 leaves, inside every outer context E ≤ 3 S's, k = 0..20:
3,248 sequences (68,208 terms, 5 min): thresholds {0: 3192, 2: 18, 3: 25, 4: 13}; no budget failures.

## E13 — orbit / context-monoid structure of M35 and BEKW Fig. 14
Left orbits β ↦ φβ: all 1,225 (φ,β) reach a fixed point; pre-period histogram {0:36, 1:1033, 2:140, 3:10,
4:5, 5:1} (max 5 for φ=β=S, the nests: classes N_0..N_7 = 0,1,2,4,8,16,16,16). For φ = s·u: max pre-period 2.
Context monoid: 460 elements (49 generators), aperiodic, max index 6, 21 idempotents — identical for M35 and
the BEKW Fig. 14 table (independent code).

## E14 — symbolic head machine searches (code/symb.py; opaque variables, never opened)
* Transfer layers: `(S Y1 Y2 x) p` with Y1,Y2 ≤ 6 leaves (65² pairs): no hnf component of the form `x Q` with
  Q a clean modification of p. In fact 4,205/4,225 runs open the predecessor x, 17 open p, 3 exceed budget —
  never an hnf (same with 2 or 3 passengers).
* Code-before-data `S g1…gj x w`: j=1 (g ≤ 8 leaves): hnf only for nests (Fibonacci peeling, x always a head);
  j=2 (≤ 6 leaves): 0 hnf (4,205 stuck on x, 17 on w); j=3 (≤ 4 leaves): 0 hnf (352 stuck on x, 1 on w, 376 budget).
* Word dynamics: nodes `S x1…xm` over 2-letter alphabets of gadgets ≤ 5 leaves (253 alphabets), words of length
  3–7, either component: 0 alphabets closed under the Böhm-tree step (junk always enters).

## E15 — closure of the Böhm-tree-finiteness congruence (sterm `closure Nr Nc 1 400 400 out`)
Sanity: with the HN oracle, `closure 7 6 0` reproduces the 35-class model (closed in 2 rounds, S-identity OK).
BT-finiteness, Nr=7: Nc=6: 32 → 45 → 51 → 61 → 68 → …; Nc=7: 33 → 46 → 52 → … (running; see data/closure_btfin_*.log).

## E16 — uniformity criterion on M35 (inline script; data: model35_hn.txt)
`S g x w`: classes with no ⊥-witness = the 6 nest classes. `S g1 g2 x w`: 0 of 1,225 class pairs escape.
`S g1 g2 g3 x w`: 0 of 42,875 class triples escape. ⇒ Corollary H1.

## E17 — Safe sets in M35 (inline script)
Safe1: 23 classes; Safe2: exactly the 6 nest classes; Safe3: ∅. Random symbolic check of H3: 20,000 random
closed K (2–22 leaves): stuck-x 10,863, stuck-y 2,598, budget(divergent) 6,539, hnf 0.
Template map (redex templates ≤ 6 leaves, ≤ 2 code slots, data x,y once each): 772 admit a safe code
assignment — all of the data-shuffling kind (e.g. `SSxy → S y (x y)`); necessary condition only.
E15 result: Nc=6 closes at 76 classes (S-identity violated on 70% of triples); Nc=7 closes at 77 classes
(violations 101,345/456,533 = 22%; the 77 representatives fall into 25 M35 classes). Neither is an S-model ⇒
contexts ≤ 7 too weak for Böhm-tree finiteness (or non-regular). Inconclusive; not pursued further.

## E18 — unbounded-deletion gadgets (code/delsearch.py; symbolic, exact)
Node `S C S^k m S^j E` (marker m, gadgets m, C, E ≤ 5 leaves, k, j = 1..4): accept if one component, with a fixed
prefix/suffix, has spine args `P ++ S^k ++ Q` for all k, j (suffix deleted) or `S^j`-only (prefix deleted).
Result: **0 of 11,638** delete-suffix and **0** delete-prefix gadgets. (Full-read loophole, "delete" mode.)

## E19 — per-symbol copy/insertion in one pass (inline symb.py script)
Node `S C σ^k E`, σ, C, E ≤ 5 leaves, k = 2..7: count the top-level spine args equal to σ in each hnf component;
flag constant slope ≥ 2 per input symbol (a doubling pass). Result: **0 configurations.** (Full-read loophole,
"copy" mode.)

## E20 — Zachos term STT(STT), T = SS (sterm `bt`, depth 14)
BT = infinite right spine whose left subtrees are `S Z_n` (Z_0 = STT, Z_{n+1} = SS Z_n) in the order
1,2,2,3,3,3,4,… — exactly as stated in BEKW §2 (Fig. 10). Infinitely many distinct subtrees ⇒ a non-regular
Böhm tree **already in BEKW** (2017). Consequence: novelty claim for Theorem C withdrawn (see STATUS R6).

## E21 — self-audits of Lemma 11, Lemma 12, Theorem N* (exact, random; code/fullread.py, audit_pot.py, audit2.py)
* Lemma 11: 2,729 terminating runs (m = 3..7 arguments ≤ 9 leaves): not-fully-read counts {0: 7, 1: 141, 2: 2,581}, 0 > 2.
* Lemma 12: 161,727 head steps, least right-depth of a tracked occurrence never drops by more than 1.
* N* (per-occurrence potential P_x): 48,648 transitions (bare variables) + 35,536 (variables under 1–3 random closed
  layers, P up to 18) along random symbolic Böhm-tree paths with x, y never opened: 0 increases (also 0 for max LD + max SUPP).

## E22 — a 39-class model for productivity (BEKW Question 5) — closure + exhaustive census
* `sterm closure 7 6 2 400 300` (ORACLE 2 = Böhm tree has no ⊥, depth cap 400): 38 classes from terms ≤ 7 leaves →
  39 → **closed in 2 rounds at 39 classes** (data/model39_productivity.txt). Contrast: the same closure for BT-finiteness
  (E15) does not close into an S-model at contexts ≤ 6 or ≤ 7.
* Finite facts (code/verify_model.py, code/prodmodel.py): S-identity holds on all 59,319 triples; generated by S;
  one non-productive class, two-sided absorbing; `S x y` productive ⟺ x, y productive and `S x` ⟺ x hold in the table;
  context monoid 951 elements, **aperiodic** (index ≤ 6). The productivity and HN (M35) congruences are incomparable
  (rep map is not a homomorphism, even on productive classes: 777 violations).
* **Census (sterm `pverify`, new mode):** model verdict vs oracle verdict for EVERY term with n ≤ 19 leaves
  (≈ 655 million terms; n = 18, 19 in 12 parallel chunks, 53 s + 205 s): **0 disagreements, 0 oracle failures**
  (n = 19: 72,605,640 productive, 405,033,060 not). Robustness: n ≤ 14 re-run with depth cap 1500 and per-node head budget
  4|t| + 5000 (instead of 400 / 4|t| + 200): identical verdicts, 0 disagreements (data/pver_*.txt, pverB_*.txt).
* Oracle sanity: Zachos `STT(STT)` productive, `AAA` not (as stated by BEKW); Theorem C's term not productive.
* Literature: quick web search (2026-10-25) found no prior productivity automaton for S; Satellite Ch. 7 not checked.
* Joint model P39 × M35 (code/jointmodel.py): 113 realised joint classes, S-identity exact, no (productive, no-hnf)
  pair ⇒ Proposition Q (soundness of C6 ⇐ BEKW Q10). ⊥_P splits into 18 joint classes (1 without hnf).

## E23 — certified non-productivity of every ⊥_P term (sterm `botcert`; completeness half of C6, exhaustive)
For each term the 39-class model puts in ⊥_P: breadth-first search over distinct Böhm-tree nodes for a node whose M35
class is ⊥ — by Theorem A that node has no hnf, so the term is certified non-productive with no reliance on step budgets
(a node with an F-class of M35 whose hnf is not found within 4|u|+1000 steps would be an ANOMALY, never counted).
Results: **every ⊥_P term with ≤ 19 leaves certified** — n=12: 29,273, 13: 119,907, 14: 477,765, 15: 1,870,144,
16: 7,237,488, 17: 27,801,511, 18: 106,279,889, 19: 405,033,060 (≈ 547M in total, equal to the E22 census ⊥ counts);
0 anomalies, 0 not found; maximal minimal depth n − 3 for every n (16 at n = 19). **Minimal certified ⊥ depth ≤ n − 3**, attained by S^{n−7}(SSS(S(SS))(SS)) (an S-nest around a
7-leaf non-productive term). Depth histogram n=12: 12,730 / 9,391 / 4,126 / 1,685 / 716 / 315 / 192 / 86 / 30 / 2 (depths 0–9).
Tooling note: a first version computed the ⊥_P class with an array pass that was mis-compiled at -O1/-O2 (correct at
-O0; spurious extra ⊥_P terms, all productive); replaced by a plain recursion, -O0 and -O2 now agree. The E22 census uses
a different (memoised) routine: re-run at -O0 for n=12 gives identical counts, and its ⊥ counts equal the certified counts.
* Minimal non-productive terms (all proper subterms productive; code/minlethal.py): n = 7..11: 2, 37, 189, 839, 3,132; the
  share without hnf (M35 ⊥) grows from 0/2 to 1,837/3,132; spine arities 3–9. No simple syntactic pattern — no shortcut to a
  syntactic proof of C6 completeness.
* Context-size stability: `closure 7 7 2` (4,707 contexts ≤ 7 S's, vs 1,275) closes at the **same 39 classes**: the table is
  isomorphic to P39 with the same acceptance set (data/closure_prod_7_7.txt) — evidence that P39 is the true syntactic
  congruence of productivity, not an artefact of small contexts.

## E24 — two-sided random test of C6 beyond the exhaustive range (sterm `prand`, 10,000 × 2 samples per size)
Sizes 20, 24, 28, 32, 36 leaves (100,000 random terms; ranks uniform modulo Catalan): every ⊥_P term certified
non-productive (Theorem A certificates; max depth 16 ≤ n − 3), every productive-class term explored cleanly (Böhm tree
finite and ⊥-free, or infinite and ⊥-free to depth 200: 2 cases), **0 refutations, 0 anomalies**. Productive terms
become rare with size (12.8% at 20 leaves, 0.8% at 36), consistent with BEKW's zero-one law.

## E25 — Angluin-style learner for finite S-models; a 131-class model for Böhm-tree finiteness
* **Learner** (code/lstar.py): classes = signatures over a growing context set E; counterexamples from (a) all terms ≤ 9
  leaves + fresh random 10–17-leaf terms, (b) the table's own observations, (c) S-identity violations (the two sides are
  convertible, so a context in E mispredicts one of them); oracle calls batched through `sterm evalfile` in 20 processes.
  Validation: re-learns the productivity model exactly (39 classes, isomorphic to P39, 33 contexts, 15 s).
* **BT-finiteness (ORACLE 1, cap 400):** converges in 63 s to **131 classes** with 68 contexts; S-identity exact on all
  2,248,091 triples; `S x y` finite ⟺ x, y finite holds in the table; 33 non-finite classes (none absorbing); joint with M35
  and P39: 416 realised classes; no class is "infinite" and hnf-free. **Context monoid: 17,031 elements, NOT aperiodic
  (period-2 elements)** — the model predicts the parity family of Theorem P2 (P = [·]S, D = S, E = [·] S S (SSS)(SS)),
  confirmed by the oracle for k ≤ 40 and then proved (PROOF.md, Theorem P2). Earlier context-closure attempts (E15) failed
  only because contexts ≤ 7 S's cannot separate these classes.
* **Census** (sterm `pverify … 1`, model file data/model131_btfinite.txt): exact agreement with the BT-finiteness oracle on
  every term with ≤ 19 leaves (≈ 655M terms; n = 19: 475,691,790 finite, 1,946,910 infinite), 0 disagreements, 0 unknowns.

## E26 — finite S-models for path properties (learner, oracles 3/4 added to sterm)
| property (MSO on Böhm trees) | classes | S-identity | context monoid | census |
|---|---|---|---|---|
| head normal form (M35, BEKW Fig. 14) | 35 | exact | aperiodic | ≤ 19 leaves (R4) |
| productive (no ⊥) — P39 | 39 | exact | 951, aperiodic | ≤ 19 leaves (E22/E23) |
| Böhm tree finite — B131 | 131 | exact | 17,031, **period 2** (Theorem P2) | ≤ 19 leaves (E25) |
| leftmost path infinite (always first component) — data/model36_leftpath.txt | 36 | exact | 809, **period 2** | 10–14 leaves exact |
| rightmost path infinite (always last component) — data/model19_rightpath.txt | 19 | exact | 184, aperiodic | learner test set ≤ 9 + random |
All learned in ≤ 63 s each. Every natural Böhm-tree property tried so far is recognised by a small finite S-model.
* Periods in the context monoids (all elements enumerated): B131 (17,031 elements): period 1 for 17,025, period 2 for 6;
  leftmost-path model (809): period 1 for 805, period 2 for 4. HN, productivity, rightmost-path: all period 1. **Only parity
  counting occurs** — every group in these syntactic monoids is trivial or Z/2.
* Satellite (Barendregt–Manzonetto) table of contents confirms Ch. 7 "Starlings" is by V. Padovani; the file is not
  accessible (HTTP 403), so whether it proves BEKW Fig. 14 (Q10) remains unknown.

## E27 — oracles for path properties; a bug fixed in nf_rec
* Oracles 3/4 (leftmost/rightmost path infinite) and 5/6 (the LO path — first component unless it normalises — ends in
  ⊥ / is infinite) added to sterm (`oracle()`); `lodbg` traces LO decisions.
* **Bug fixed (2026-10-25):** `nf_rec` memoised a bogus normal form for a term whose recursive normalisation had failed;
  a later call in the same generation then reported "normalises". It made the LO oracle misjudge T_3 = SSSS(SSS)(SS)
  (cross-checked against an independent Python trace, which now agrees step by step). Affected only modes that call
  nf_rec repeatedly in one generation (`spine` side-component prints, the new LO oracle); census/certified results use
  hnf directly or one nf_rec per fresh generation and are unaffected.

## E28 — certified finiteness for every finite-class term ≤ 19 leaves (sterm `fincert`)
For each term the 131-class model calls finite: depth-first exploration of its Böhm tree over distinct nodes; a node whose
M35 class is ⊥ is a certified ⊥ leaf (Theorem A); every other node's hnf is computed exactly (else ANOMALY); a node met
again on the current path would show an infinite tree (CYCLE-REFUTES). Result for n = 7..19: **every finite-class term
certified** (n = 19: 475,691,790; n = 18: 129,049,682; …), 0 anomalies, 0 cycles, 0 too deep; maximal depth 63 (n = 19).
Hence for |t| ≤ 19 the 131-class model's "finite" verdicts are unconditionally correct; its "infinite" verdicts are
correct for all t given BEKW Q10 (Proposition Q′) — now proved (Theorem Q10).

## E29 — a 204-class model for "the leftmost-outermost evaluation path is infinite" (ORACLE 6)
LO path: at S p q go to p unless p normalises, else to q (the path leftmost-outermost evaluation follows). Oracle bounded
after a first run stalled (>1 h on expensive normalisation checks): nf budget 3000 per check, node size ≤ 200,000,
depth cap 120; resource exhaustion counts deterministically as "p does not normalise / path continues". Learner:
**204 classes, 107 contexts, 336 s; S-identity exact on all 8,489,664 triples**; 34 accepting classes; joint with M35 and
P39: 424 classes, no accepting class is hnf-free; context monoid 45,486 elements with period-2 elements (parity again).
Census against the bounded oracle (cap 120): **every term ≤ 18 leaves agrees** (≈ 178M terms; n = 18: 589,063 infinite
LO paths, 129,055,727 finite), 0 disagreements, 0 unknowns. Up to 12 leaves 'LO path infinite' coincides with 'Böhm tree
infinite' (4, 19, 61, 227, 629 terms); from 13 leaves they differ (5, 24, … terms with an infinite Böhm tree but a finite
LO path). (data/model_lopath.txt)

## E30 — a 423-class model for branching infinity (ORACLE 7: some node has two components with infinite Böhm trees)
Oracle: breadth-first over distinct nodes to depth 40 (≤ 4000 nodes), each two-component node tested with the
BT-finiteness oracle (cap 160) on both components. Learner: **423 classes, 109 contexts, converged in 3,533 s with 0
counterexamples; S-identity exact on all 75,686,967 triples**; 84 accepting classes. Counterexamples rose late
(24 at round 20) and then vanished — real distinctions, not oracle noise. Counting: 4,000 random context maps have
periods {1: 3,999, 2: 1} — parity only (C10). **Census: every term ≤ 16 leaves agrees with the oracle** (≈ 13M terms;
n = 16: 56,278 branching, 9,638,567 not), 0 disagreements. (A loader limit of 256 classes in sterm.c caused segfaults on
this 423-class model; stride raised to 1024, earlier models unaffected.) (data/model423_branch.txt)

## E31 — bounded re-opening in head runs (code/opencount.py, code/opencount_rand.py) — 2026-10-25
Provenance head machine: an element is (occurrence of the original term, appended extras); opening it opens that
occurrence. For every M35-F term with 3–13 leaves (224,716 terms, all head-normalising) the largest number of openings of
one application occurrence is **2** and of one leaf occurrence **4** (4 only at 9 and 10 leaves, e.g. S(SSS)SSSSS and
S(S(S(S(SS))S)S)SS; 3 elsewhere). n = 13: leaf maxima {0: 117,572, 1: 39,683, 2: 1,652, 3: 133}, application maxima
{0: 141,285, 1: 17,643, 2: 112}. Diverging runs (⊥ terms, 8–11 leaves) open some occurrence 31–124 times within 200 steps.
Random F terms (about 2,000 of 3,000 samples each at 20/30/40 leaves): maxima 2 (application) / 3 (leaf), but those runs are short (≤ 14 steps),
so this is weak extra evidence. Recorded as Conjecture C12 (PROOF.md). (data/opencount_13.txt)

## E32 — non-idempotent type certificates for Question 10 (code/nitypes.py, code/nicert.py) — 2026-10-25
Canonical derivations (Lemma 14) built by subject expansion along each head run. Types of argument occurrences over all
F terms ≤ n leaves: 1, 1, 1, 2, 3, 6, 15, 31, 58, 69, 73, 77 distinct types for n = 1…12, depth ≤ 14 (class s = S
carries the most: 39 at n = 12). Certificate search (all occurrence types incl. head S and spine prefixes, Θ from F terms
≤ 7 leaves, 7 repair rounds): magma M35 × P(Θ) generated by (s, V(S)) has 58–72 elements; failing F elements 7 → 6,
classes {12, 21, 24, 26, 28, 29, 31}; failing representatives include the left combs S^k (k growing each round) and
SSS(SSS)SS, S(SS)(S(SSS))SS, SSS(S(SSS)S)S; Θ grows 34 → 111 types, depth 8 → 20. Proposition T proves that no finite Θ
can work (left combs). The S-types of S^k follow τ_{j+1} = [τ_j] → [] → T_j, T_j = [τ_{j−1}] → T_{j−1}.

## E33 — literature: local termination (2026-10-25)
Endrullis, de Vrijer, Waldmann, "Local Termination: theory and practice", LMCS 6(3:20), 2010 (arXiv 1006.4955), read
from the arXiv PDF: partial monotone algebras; semantic labelling with a partial model turns local termination on a
regular set into global termination; applied to S they label the S-rule with the automaton for the normalising S-terms,
obtaining 1,800 labelled rules whose global termination TTT2 proved and CeTA certified — a machine-checked proof of
Waldmann's normalisation characterisation. Their method needs SN = WN on the target set (true for full reduction on
normalising terms, false for head reduction on head-normalising terms) and finitely labelled interpretations, which our
items 14–16 and 19 show cannot certify Q10 with M35 labels. Not an answer to Q10; it explains why BEKW left it open.
The user-pasted Satellite excerpt (2026-10-25) is FSCD 2023 (Manzonetto) lines 257–270, already in literature/.

## E34 — Theorem Q10: tail-chain certificate (code/tailchain.py, refillgraph.py, q10_chaincert.py) — 2026-10-25
Tail chains of the big-step recursion for all M35-F terms ≤ 12 leaves: length ≤ 9, at most 2 refills per chain (e.g.
S(S(SSS))S(S(S(S(S(SS))))): P R P P P P P P e). Lemma 15: no M35 product equals s (so class s = {S}). Abstract chain
graph on (class p, class q, class v) with peel and refill edges: 8,329 states, 85,367 edges (84,206 after excluding refill
targets with q = S), every SCC a singleton; the only refill self-loop, (13, 0, 16), needs a refill whose new second
component is S, which cannot happen. networkx re-check: acyclic apart from self-loops, 0 refill self-loops, 1 peel
self-loop; all 15,923 concrete chain transitions of F terms ≤ 12 leaves are edges of the right kind. M35 facts re-verified
(S-identity 0 violations of 35³, ⊥ left-absorbing, S/Sx/Sxy in F, right-multiplication graph minus self-loops acyclic,
only F self-loop 12·s). → Theorem Q10 (PROOF.md).

## E35 — Böhm-tree path certificates for the remaining halves (code/btpathcert.py, leftpathcert.py, pathcert2.py)
Joint models: B131 × M35 (221), P39 × M35 (113), L36 × M35 (69), R19 × M35 (78). Coarse test (computed edges = children c,
b c of nodes with ≥ 3 arguments): computed edges inside SCCs — C8 half 157 (SCCs 37, 10, 5, …), C6 completeness 56
(one SCC of all 17 classes), leftmost 2 (SCC {(14,28),(14,26)}), rightmost 71 (SCC 20). Refinements (chain length 0 ⇒
child is the last argument; composite nodes tracked by the classes of their parts, 3,429 path states) do not remove the
leftmost SCC. Sampling 148,138 random terms (8–22 leaves) in classes (14,28)/(14,26): leftmost paths take 0–5
size-increasing steps (132,497 / 14,226 / 1,217 / 169 / 24 / 5), alternating with decreasing ones — a nested counter.
Closure facts of L36 and R19 verified (→ Proposition Q″).

## E36 — leftmost-path finite half: measures, probes, mechanism (2026-10-25)
* **Measures tested and failed** (code/piecewalk.py, basewalk.py, newnodes.py, inline): (a) multiset of provenance pieces
  per step — fails on 1/18/99 flag-0 terms at 8/9/10 leaves (duplicated S-leaf pieces); (b) base occurrence strictly
  descending at size-increasing steps — fails (74 flag-0 terms at 11 leaves inside classes 26/28, often S-leaf bases);
  (c) pieces / size between consecutive size-increasing nodes — pieces fail on 116 of 45,682 random flag-0 terms
  (cases ending in ⊥ right after), size fails 698 of 1,700 times inside classes 26/28.
* **Chains of size-increasing steps inside {(14,28),(14,26)}** (≤ 11 leaves): patterns PE 483, RPE 274, PPE 194, PPPE 54,
  RPPE 49, RE 41, …; almost all end with a peel from p = SS, so the new node is q_pen v_pen and the walk then drops to v_pen.
* **Probe census** (code/probe.py, t z z with a variable z): ≤ 10 leaves — the one infinite-leftmost term has a diverging
  probe (Lemma P); paths ending at S: probe converges for 3,793 terms at 10 leaves, diverges for 45 (6 at 9 leaves);
  paths ending in ⊥: probe always diverges (1,023 at 10 leaves).
* **Mechanism of infinite leftmost paths** (smallest example S(S(SS))(S(SS))(SS)S, 10 leaves, joint class (9,28)): every
  node is (SS)^j B · M · S with B = S(SS)(SS); the first slot counts down an SS(·) nest and, at the base, reloads with one
  more layer — a self-incrementing counter (as in Theorem C). The finite family S S N X Y (class (14,28)) counts down once
  and stops. Infinite leftmost paths live entirely in the two-argument-dead classes D2 (Theorem LP1).
* **Open-term model** (code/lstar_z.py, Python oracle with M35 shortcuts): 18 classes after 4 rounds, then the class
  table grew too slowly to finish in Python; needs a C oracle. All variable-headed terms form one absorbing class σ
  (σ·x = σ), which breaks the rank argument of Theorem Q10 for σ-rooted runs — the open analogue of Q10 needs a separate
  argument for σ. Substituting closed terms for z only recovers the closed (D2) information.

## E37 — reload counters and attempt 1 (2026-10-25)
* Counter-shaped candidates (SS)^j B M R, S S K M R, S K M R with parts ≤ 5 leaves: 49,726 built, 14,122 in flag-0 D2
  classes; every leftmost walk ends within 18 nodes (6,575 at S, 7,547 in ⊥) — no indefinite reloading.
* Infinite mechanism verified for all k: N_i N_k S ↦ N_{i−1} N_k S (i ≥ 1), B N_k S ↦ N_k N_{k+1} S, B = S(SS)(SS).
* Inside {(14,28),(14,26)}: 1,869 transitions between consecutive size-increasing nodes mix decreasing, copied and growing
  slots; node size fails 698/1,700, the argument-size multiset between growth points fails 73/82.
* Attempt 1 (symbolic size-change abstraction): see FAILED_APPROACHES 22.

## E38 — infinite head runs (leftmost-outermost evolution of hnf-free terms), 2026-10-25
code/loopsearch.py: no closed code ≤ 8 leaves reproduces itself as the front element over data within 60 steps; control
prefixes repeat only just before a datum reaches the front (data take control). code/opcodes.py over all 892 hnf-free
terms ≤ 10 leaves (6,000 steps): 462 eventually periodic, 256 single linear counters (increment ≤ 1 per period),
31 driven by other opcodes, 143 periodic with rare insertions; no two-counter behaviour seen.

## E39 — three-slot leftmost-walk counter programs, 2026-10-26 (disprover)
code/walk3.py 4 2 8: nodes ((N_i N_k) N_m) R with SS-nests over bases ≤ 4 leaves, tails ≤ 2 leaves, 8 walk steps, exact
symbolic case splits: 262 guarded transitions, all plain decrements of one slot; 0 transfers, 0 slots both incremented
and decremented. Bounded search, not a proof.

## E40 — head-style depth along head runs, 2026-10-26 (disprover)
code/hsdepth.py (random configurations, z opaque, 300 steps): the maximal number of head-style frames around an occurrence
of z rises in 339 of 2,432 runs ('directly followed by a closed argument') and 287 of 2,487 ('followed anywhere later');
smallest example: [S(Sz), SSz, S(S(SS)S), SS(S(S(SS)S)), S(SSS), SS], depth 1 → 2 after two steps. Fuel (closed elements
below data) can multiply once one violation exists (PROOF.md, disprover round).

## E41 — Theorem U* and Corollary W, random exact check, 2026-10-26 (disprover)
code/corw_check.py 4000 120 7: 4,000 F1/F2 runs with marked closed occurrences (tags x, y), 364,712 steps, 81,735 zero
tests (openings of marked occurrences): 0 violations of F1/F2; 2,135 runs also J1/J2: 173,753 steps, 12,265 clean writes
onto y-elements, none while an element containing x but not y existed; 0 violations of J1/J2.

## E42 — the sawtooth loop, traced, 2026-10-26
code/sawview.py 140 4: the head run of t z z (t = S(S(SS))(S(SS))(SS)S) passes the templates [S, N_i, N_k, S, …] with
(i, k) → (i−1, k) every 5 steps and (0, k) → (k, k+1) via [SS, SS, N_k, S] (the base S(SS)(SS) writes SS onto N_k); agent U
derived the rules symbolically for all values (PROVER_LOG entry 1: 5 / 7 / 6 steps).

## E43 — writes behind a live control versus initial fuel, 2026-10-26 (disprover)
code/fuel_check.py / fuel_check2.py (6,000 random J1/J2 lists with marked x, y occurrences, not F1/F2, 200 steps): counting
a write only when an x-only element survives it, 56 runs make more writes than their initial fuel (max 28). Traced cases:
the writer is a fresh constant unit S·x extracted from the target itself (the target holds copies of a one-step control),
not a regenerated supply for a decreasing counter — so no fuel-regeneration gadget and no counterexample to a fuel law for
counters; a law must be stated per counter lineage.

## E44 — access lemma and Lemma G1, random exact check, 2026-10-26
code/geom_check.py 6000 150 5: 273,888 cases of an old element (position ≥ 3) entering positions 1–2 — always the copy
of c with |ch(a)| ≤ 1 and b·c directly below; 240,328 steps with the lowest y-element off the front — the region below
it always unchanged or minus its top element. 0 violations.

## E45 — closed code never rebuilds itself (bounded), 2026-10-26
code/selfrep.py 10 300: for all 6,917 closed terms Q with 2–10 leaves, the head run of [Q, x1, x2, x3, x4] (x_i opaque)
for 300 steps: 5,643 reach an opaque datum at the front (data take control), 1,274 diverge in pure code; in none does Q
reappear as the front element or directly above an opaque datum. So loops must be data-driven (as in the sawtooth, where
the counter N_k is executed as the loop body); a target cannot be rebuilt by closed code alone in this range. Bounded
evidence, not a theorem.

## E46 — head-style pump transfer and reload search, 2026-10-26 (main agent)
Round rule with targets X_k = S S X_{k−1} S over S(SS)(SS): k rounds of T(k, n) ↦ T(k−1, n+1) verified exactly (prefix
through r1 after every round) for k ≤ 6, n ≤ 5 (e.g. 69 steps for k = 6, n = 5). code/pumpreload.py 8 4 600 (every closed
base ≤ 8 leaves, n = 0..4, 600 steps, opaque tail): 232 stuck, 2,896 still running without re-entry, 2 'reloads' — both
the coincidence base = S, n = 3, 4 (three absorbed S's equal X_1(S) = SSSS), after which the run sticks.

## E47 — behavioural complexity of all infinite head runs up to 11 leaves, 2026-10-26 (main agent)
code/factorcx.py + code/cxclassify.py (fixed: the last, truncated block is dropped; runs without long blocks are tested
on the gaps between occurrences of an opcode): all 4,092 hnf-free terms with ≤ 11 leaves, 8,000 head steps, opcode =
spine length of the opened front element (capped at 3). Factor complexity bounded or ~linear: 3,189; superlinear but a
single affine counter (block lengths L_{j+p} = L_j + c_{j mod p}): 870 (blocks) + 21 (gaps); remaining 12: two-level nested
counters of sawtooth type (e.g. S(SSS)(S(SS))(SS)(SS): block value 14 twice, 18 three times, 22 four times, …;
SSS(SS)S(SS(SS)): gaps 9, 15, 9, 18, 9, 15, 9, 19, … with slowly growing peaks). The most complex-looking runs by raw factor
complexity are single counters (block lengths 5,5,5,5,5,6,5,6,6,…). No run shows two interacting counters or anything
beyond nested linear counters. EXPERIMENTALLY SUPPORTED (bounded census).

## E48 — template-free growth search and layer census, 2026-10-26 (main agent)
growth_search.py (families N, X r = 1, 2, XN; bases ≤ 7 leaves; 4,000 steps; bare and nested counter depth in the top 4
entries) and growth_code.py (closed control C ≤ 5 leaves in front, bases ≤ 5 leaves, NN/XX/XN/NX, 2,400 steps): only the
sawtooth grows (40 control prefixes; one NX hit is the sawtooth carrying X_1 as fuel). layer_ops.py 7 4 160 N/X: every
one-hole context ≤ 7 leaves that reaches the next node shifts the supply by a constant c ≥ 0 (c = 0..6); no decrement;
zero-test layers S(SS)(SS[]), S(SS)(SS([]S)).

## E49 — flat iterator, tape-driven growth, two supplies, 2026-10-26 (main agent)
Flat iterator S·S^n·B·S → S·S^{n−2}·B·S verified for n = 2..11, B ∈ {N_1..N_3, X_1..X_3} (n+3 / n+4 steps). growth_tape.py
4 2400: 324 runs over closed tapes, 0 growing. two_supply.py 6 300: no recurring two-supply node for any marker ≤ 6 leaves.

## E50 — flat → nest rebuild search, 2026-10-26 (main agent)
rebuild_search.py 6 1500: 384 runs (C ≤ 6 leaves × {X, N} × n ∈ {4, 6, 8}); 9 flagged runs are sawtooth growth independent
of n (comb shrinks once, then constant); no flat→nest transfer.

## E51 — Lemma SM, random tests, 2026-10-26 (main agent)
code/sm_check.py (B compared as a term): 600,000 random runs, the next-node form reached 16,270 times, 2,246 'violations'
m < n, all lookalikes with tiny bodies (B = S, SS, SSS built from supply leaves) — the term-matching statement is false.
code/sm_check2.py (B a marked occurrence, tracked by identity): 600,000 runs, form reached 13,731 times, 0 violations,
m − n ∈ {0, …, 5}.

## E52 — Wolfram's exponential S-expressions under leftmost-outermost evaluation, 2026-10-26 (main agent)
Source: Wolfram, NKS notes (wolframscience.com/nksonline/page-1122a): s[s[s]][s][s][s][s] = S(SS)SSSS is the shortest
expression with unlimited growth (size ~2^(t/2) under expr /. rules, i.e. parallel outermost rewriting), and
s[s][s][s[s]][s][s] = SSS(SS)SS behaves alike (the 'random-fluctuation' examples there contain K). Under leftmost-
outermost evaluation (code/lo_bt.py): both have an hnf after 9 / 8 head steps with the same components; the first component
normalises and LO settles into the second, S(S(SS)S)S(S(SS)(S(S(SS)S)S)) (15 leaves, M35 class 33, no hnf) — an infinite
head run. That head run (30,000 steps): factor complexity 26/42/74/138 (m = 8..64), opcode-2 blocks 144, 143, 145, 144, 146,
… (affine-periodic, period 2), list length linear (~0.93 per step): a single linear counter. So the exponential growth
seen by Wolfram is Böhm-tree growth under parallel rewriting; the leftmost-outermost evolution of the same terms is as
simple as the census predicts (consistent with Conjecture R′ at 15 leaves).

## Bug notice, 2026-10-26 (main agent): stale-id caches in lo_bt.py and growth_search.py
lo_bt.cls and growth_search.maxd cached values by Python object id without keeping the object alive; recycled ids could
return a stale value for a different term. Fixed (the cache now stores the object and checks identity). Affected: the
deep-mode growth searches (E48 'counters nested anywhere', growth_code.py) and E49's tape search (growth_tape.py), plus
first runs of lo_census.py / random_cx.py (discarded). E52's classes were recomputed with the fixed function: unchanged
(28, 28; the 15-leaf endpoint class 33, no hnf). Other scripts use per-call caches (all objects alive) or already keep
references (agent_u_fuel.py) — unaffected. Reruns follow (E53).

## E53 — reruns after the cache fix, 2026-10-26 (main agent)
growth_code.py 5 5 2400: output byte-identical to the pre-fix run (40 growing runs, all sawtooth). growth_tape.py 4 2400:
324 runs, 0 growing. growth_search.py 7 3000 {X, XN} 1 deep: 528 runs each, 0 growing. The stale-id bug did not change any
recorded conclusion of E48/E49.

## E54 — BINARY COUNTERS in head runs; correction of E47; Conjecture R′ refuted, 2026-10-26 (main agent)
The census's 'unexplained' runs were re-examined over 120,000–150,000 head steps (gaps between occurrences of opcode 2):
SSS(SS)S(SS(SS)) (10 leaves), S(SS)SSS(SS(SS)), SSS(S(SS)S)(SS(SS)) and, from the random sample of 15–22-leaf hnf-free terms,
SSS(SSS(SS)S(SS(SS)))(S(S(SS)(SS))S), SS(SS)SS(SS(SSS)(SS)S)(SS(SS)) and three more: the long gaps alternate 9 with values
15 + 6·v2(k + 4) (v2 = 2-adic valuation): 21 mismatches in 2,000 (entries 200–2,200) for the 10-leaf terms, 51 in the first
2,000 (all in the transient) for the larger ones; value frequencies 15: 2,348, 21: 1,172, 27: 584, 33: 290, 39: 143 — the
ruler distribution. These head runs are BINARY COUNTERS (carry propagation of length v2(k)).
CORRECTION of E47: SSS(SS)S(SS(SS)) and its variants were wrongly called 'two-level nested counters'; they are binary
counters. S(SSS)(S(SS))(SS)(SS) is a genuine two-level nested counter (value 4j + c repeated about j times).
Random sample (random_cx.py 1500 15 22 8000 7, after the cache fix): 1,317 bounded/linear, 149 + 21 single affine counters,
13 other: 9 two-level nested counters, 4 binary counters.
CONSEQUENCE: the ruler sequence is not piecewise-affine in any period, so it cannot be produced by the copy/reset/
increment machines of Proposition MM — Conjecture R′ (PROOF.md synthesis) is REFUTED as stated: head runs can modify the
interior of a structure (carries), contrary to the operation catalogue O1–O5.

## E55 — binary counter driver, call words, call algebra, 2026-10-26 (main agent)
* code/driver_proof.py (macro derivation, level k symbolic): C1(k) → C1(k+1) in 26 head steps + 7 macros, valid for every
  k ≥ 1 (fails only if k = 0 is allowed); the unknown rest of the list never reaches the top three. code/driver_check.py:
  derivation's cycle length = 144·2^k − 48 for k = 2..6; concrete run of SSS(SS)S(SS(SS)) has C1(k) on top exactly at
  t_k = 144·2^k − 48k − 104 for k = 2..12 (11/11, up to step 589,144).
* code/call_step_check.py: symbolic inductive step of the call lemma for every j ≥ 2: trace A [call j−1] B [resume j−1];
  base cases j = 0, 1 concrete. code/driver_words.py: A constant (m ≥ 1), u_m = w_{m−1}·B·u_{m−1} for 2 ≤ m ≤ 12; the
  predicted opcode word (transient · D_2 · D_3 ⋯) equals the real opcode word on all 589,144 steps.
* code/same_counter.py: the other four binary counters of E54 hit the same C1(k) at t_k + δ, δ = +1, −2, +2, +8.
* code/scheme_search.py 7 5 40000: 39,874 (base, context) pairs; schemes whose P_0..P_5 are all calls: linear 1,484,
  ×2 92, ×3 8 (data/scheme_search_7.txt). code/kary_check.py: k-ary schemes T_{m+1} = kT_m + k for k = 1..6 (x·y at front,
  tape never touched). code/call_algebra_check.py: 225 random tree calls, composition rule T = ΣT(A_i) + k, 0 mismatches.
* Correction: PROOF.md's closed form for the call time was 2^{j+3} − 8; it is 2^{j+4} − 8 (values were right).

## E56 — sharper LO census to 12 leaves (lo_census2.py 12 30 12000), 2026-10-26 (main agent)
Terms ≤ 12 leaves: 44,583 normalise, 36,977 reach a 'bottom' endpoint, 940 deeper than 30. Distinct hnf-free endpoints:
18,326 — bounded/linear 14,853, single counter 3,321, binary counter 111, nested counter 1, OTHER 40
(data/lo_census2_12.tsv). Follow-up (code/census_followup.py): only 21 of the 111 binary counters reach the C1(k) states of
Theorem BC within 20,000 steps — binary counting occurs through several different machines; 37 of the 40 OTHER endpoints
have base-2 ruler laws with other parameters (gaps 14+2j, 15+2j, 17+2j, 20+3j, 26+3j, 39+8j, 43+8j; frequencies halving);
the remaining 3 are a nested counter with growing values (S(SS)S(S(S(SSS)(SS)))S) and two runs whose front spine length
grows without bound (S(SS)S(S(S(S(SSS))S))S, S(SS)S(S(S(SS(SS))S))S; opcodes up to 51 after 200,000 steps).
No base-3 law below 13 leaves.

## E57 — k-ary schemes, S-numerals, a spontaneous ternary counter, 2026-10-26 (main agent)
* code/rand_radix.py 40 12 24 30000 11: 1 of 40 hnf-free random terms has a base-3 ruler law:
  S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(SSS(SS)))) (23 leaves). 400,000 steps: gap families 6+3j and 7+3j with frequencies in
  ratio 3 (3420:1143:381:127, 10261:3421:1140:379); opcode-4 gaps 141, 479, 1493, 4535, 13661, 41039, 123173 = 3g + 56.
  Recurring calls L_m (code/explore_levels.py): sizes 24 + 8m, T_{m+1} = 3T_m + 10 for m ≤ 6.
* code/gadget_scan.py 7 5 300000: multiplier gadgets (see PROOF.md 'S-numerals'). code/numeral_check.py: Theorem N's two
  formulas 30/30.
* Theorem TC certification (code/tern_check_all.py 9 9): T_m = 13·3^m − 5 for m ≤ 9 with return top [Z, V′Z, (Z(SZ))(V′Z)],
  tape untouched; call-word recursion m ≤ 9; C1′(k) on top at t′_k for k = 1..9; opcode word identical on 1,407,063 steps.
* Radix detector caveat: the 'base 4/5/6' hits of rand_radix.py (4 + 1 in 1,500 random terms) and driver_family.py were
  checked with explore_levels.py / explore_config.py: their calls follow ×2 schemes (T_{m+1} = 2T_m + 9 or + 8; the 4-adic
  statistics come from a driver that climbs two levels per cycle) or are linear. Only bases 2 and 3 are confirmed in real runs.
* code/body_search.py 9 400: no loop body ≤ 9 leaves transforms the accumulator of a numeral loop except the identity (SS).

## E58 — gadget drivers: counters in every base, 2026-10-26 (main agent)
* code/gadget_driver.py / gadget_driver2.py: the driver configuration [L, SSX·L, L(SL)(SSX·L)] with levels
  L_{m+1} = S(S S X L_m) works (return top preserved, C1(k) → C1(k+1)) when the base's c-part is S(S(SS)S)(SSX); the b-part is
  irrelevant (5 choices tried). Works for X = SSS(SS) (×3), SS(SSS(SS)), SS(S(SS)SS) (×4), SS(SS(SSS(SS))) (×5); not for
  SS, SSSS, SS(SS), SS(SS(SS)), SS(SS(SS(SS))), SSSSSS, SS(SSSS) (return top not preserved).
* code/kcounter_proof.py 7, kcounter_general.py, kcounter_base.py: symbolic derivations (Theorem K). code/kcounter_certify.py
  8 7 3000000: predicted C1(k) times confirmed for μ = 3..8.
* The two census runs with unbounded opcodes (E56): code/newmax.py on S(SS)S(S(S(S(SSS))S))S — the step gaps between new
  opcode maxima have second differences exactly 56, 65, 74, …, 281 (+9 each, k = 5..30): time to reach spine length k is a
  cubic polynomial in k; the front element at each new maximum grows ×6.0 in tree size per level (shared DAG). A regular
  nested counter, not a counterexample to R″. code/capped_cx.py (opcodes capped at 3, 600,000 steps): p(n) ratios
  2.1, 2.5, 3.1, 3.6 for n = 8..128 (consistent with quadratic complexity); the jumps at n ≥ 256 hit the sample-size limit
  and are not interpretable. Binary counter SSS(SS)S(SS(SS)) for comparison: ratios 2.15 … 2.04 (linear).

## E59 — the same terms under Wolfram's parallel (ReplaceAll) evaluation, 2026-10-26 (main agent)
code/parallel_eval.py (one pass contracts every outermost non-overlapping redex, top-down; memoised per DAG node):
* SSS(SS)S(SS(SS)) (the Theorem BC binary counter under leftmost-outermost): no normal form in 120 passes; sizes 10, 11,
  11, 14, 17, 20, 24, 32, 49, 83, …, 1.67·10^24 at pass 120; size ratio drifts slowly downward (1.607 at n ≈ 66, 1.600 at
  90, 1.599 at 120); no exact linear recurrence of order ≤ 10 on 91 sizes (code/size_recurrence.py).
* S(SS)SSSS and SSS(SS)SS (Wolfram's examples; under leftmost-outermost a single counter): ratios still drifting upward
  after 120 passes (1.609 → 1.635).
Reading (CORRECTED below): under parallel evaluation these runs show no sign (yet) of the exact recursive structure they
have under leftmost-outermost; none of our leftmost-outermost theorems apply there.
* Shape (code/parallel_shape.py, passes 0–45 of SSS(SS)S(SS(SS))): the head spine grows irregularly (5, 4, 4, 3, …, 10
  at pass 22, 16 at 34, 19 at 45); small 'datum' sizes recur at the front of the spine in phases (70 at passes 17–21, 100 at
  26–31, 157 at 39–44, each followed by n+1, 2n+1, …) and a fixed-size element (51 leaves) drifts one place right per pass
  from pass 33 on, while the deeper arguments grow by their own internal reductions. Structured, but not yet described.
* τ3 = S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(SSS(SS)))) (Theorem TC's ternary counter): no normal form in 70 passes, sizes
  23, 25, 26, 32, 41, …, 7.8·10^14; ratio drifting upward 1.626 → 1.644 (passes 47–70).
* Linear complexity (code/bm_sizes.py, Berlekamp–Massey over three primes; calibrated: Fibonacci L = 2, Fibonacci + n²
  L = 5, 2^n + 3^n L = 2): SSS(SS)S(SS(SS)) L = 61 of 121 sizes (51 of 101 from n = 20, 41 of 81 from n = 40), S(SS)SSSS
  61 of 121, τ3 36 of 71 — all maximal: no linear recurrence of order below about half the length. CORRECTION of the reading:
  this is generic — all 319 non-normalising terms with 6–9 leaves have maximal L on passes 10–60 (code/bm_scan.py 6 9 60).
  So no small S-term's parallel size sequence is linear-recurrent (parallel evolution is never a small D0L system there),
  but the test does not single out complex behaviour: sequences built from internal counters at different stages
  (k-regular-type) are simple and still not linear-recurrent. No conclusion about complexity under parallel evaluation.
* Tree calls under parallel evaluation (code/parallel_calls.py, parallel head machine of Lemma PH, atomic x, y, tape):
  the k-ary levels P_0..P_4 (k = 2, 3) bring x·y to the front after exactly the head-machine time (2, 6, 14, 30, 62 and
  2, 9, 30, 93, 282 passes). Random mixed tree calls (code/parallel_calls2.py, T ≤ 4000, shared memo): the parallel time equals the head-machine time
  in all 50 compositions tested before the 25-minute limit (0 differ).

## E60 — random hnf-free terms with 30–40 leaves, 2026-10-26 (main agent)
code/fast_classify.py 1500 30 40 40000 202 (fast hash-consed run; classes as classify2.py plus radix): 1,473 bounded/linear,
16 single counters, 9 base-2 counters, 2 'OTHER' (data/fast_classify_30_40.txt). Both 'OTHER' runs are binary counters the
classifier missed (its radix detector picked a longer spurious chain): S(S(SS)(S(SS))S)(SS)(SSS(SS))(SS(SS)(S(S(SS(S(SS))S(SS))
(S(S(SS)))))) has opcode-3 gaps 8j with halving frequencies and level gaps g_{n+1} = 2g_n + 58 (1382, 2822, 5702, 11462);
S(SSS)(SS)(SS)(SSS(S(SS(S(SS))(S(SS))))S)(SS(S(SSS)S))(S(SS)SS(SS)S) has two interleaved level families
g_{n+1} = 2g_n + 11 (149 … 2549) and 2g_n + 13 (387 … 6387); capped-opcode factor complexity ratios → 2 for both.
So 1,500 of 1,500 sampled head runs at this size are bounded, single counters or binary counters — no new phenomenon
(EXPERIMENTALLY SUPPORTED evidence for Conjecture R″).
* Loop-body searches (2026-10-26): code/body_search.py 12 400 — of all bodies ≤ 12 leaves only SS returns to the loop
  with an accumulator over A and S (the identity); no near misses. code/body_search2.py 11 400 (control may return with extra
  arguments X·Z·w…): 4,367 bodies return to the loop, 0 transform the accumulator, 0 near misses.
* Parallel head spine of SSS(SS)S(SS(SS)) for 160 passes (code/parallel_spine.py, data/parallel_spine_BC.json; the shared
  DAG grows ~40× per 50 passes — 13·10^6 nodes at pass 150 — which limits the length): grows roughly linearly (77 at pass
  160, ≈ 0.48 per pass). From pass 38 the differences repeat the motif 1 1 1 0 −1 0 every 8–12 passes; every second
  segment between motifs is exactly 2 −1 2 (passes 90, 109, 129, 150) and the others grow slowly (3 0 1 0; 0 1 0 1 0;
  2 0 1 0 1 0). Quasi-regular — a fixed skeleton interleaved with a slowly growing component, like a nested counter —
  not chaotic on this window; EXPERIMENTALLY SUPPORTED only (160 passes).
* Clock readouts (code/clock_spines.py 9 60): of the 319 non-normalising terms ≤ 9 leaves, 168 reach a constant head
  spine under parallel evaluation (125 with spine 2, 43 with spine 1 — head-normal shape, time is stored in their
  arguments) and 151 have spines growing roughly linearly with small fluctuations (e.g. S(SSS)S(SSS): 9, 11, 12, 11, 12,
  13, 12, 13, 14, 13, 15, 16 for t = 20..31); none is exactly linear or periodic. So a clock gives a noisy unary readout
  of elapsed time; a clean branch selector would need a designed clock.
* Clock candidates with longer runs (code/clock_spines.py 11 40, code/clock_long.py, code/clock_struct.py): the
  'periodic differences, p = 8–12' classes of the 40-pass scan are window artifacts — S(SSS)S(SSS) (DAG stays small)
  shows no period ≤ 40 over passes 500–1000. Its head spine reaches 577 at t = 1000 and 928 at t = 1600; slope drifts
  upward slowly (0.540, 0.552, 0.564, 0.573, 0.580 at t = 100, 250, 500, 750, 1600); differences take only the values
  −1, 1, 2, 3; their factor complexity is about linear (4, 7, 12, 20, 28, 44, 80 for lengths 1–64); window sums stay in
  narrow bands (100-pass windows: 56–62). Quasi-regular, like a nested counter with slowly increasing density — a
  structured but not exactly predictable clock (data/clock_SSSS_spine.json).
* Clock steering in the robust counter K0 = S(SS)S(S(S(SSS)))S (code/clock_steer.py 1500, one process per variant): with a
  clock W (SSS(SS)S(SS(SS)) or S(SSS)S(SSS)) appended as a last argument, the leftmost-outermost and parallel runs do not
  differ in the observed windows (134 and 354 steps — K0 never reaches its last argument); with W substituted for any
  one S leaf of K0, the runs differ within 6–26 steps, but the variant is no longer a counter under either order (no
  radix law; runs limited to 134–681 steps by the clocks' growth). No steering observed: naive placements either never
  read the clock or destroy the driver; a designed clock reader is needed.
* The robust counter K0 = S(SS)S(S(S(SSS)))S (code/run_profile.py, newmax.py, flat_digits.py, explore_levels.py): a binary
  counter of a different kind from Theorem BC — its only recurring call is S(SSS) (T = 3), its opcodes stay ≤ 4, opcode-0
  gaps are 6, 8, 10, … with exactly halving frequencies (9378, 4689, 2345, …), opcode-3 events are exactly 2^{k+5} − 5 steps
  apart: at steps 32·2^k − 5k − 10 (k = 0..8: 22, 49, …, 8142), where the list length is 20·2^k − 6k − 11 (9, 23, …, 5061).
  The list elements are mostly new, growing shapes (not a fixed digit alphabet). COMPUTATIONALLY CERTIFIED for k ≤ 8;
  its symbolic theory (and hence a proof that it is parallel-robust forever) is open.
* K0's opcode word (code/k0_words.py, k0_morphic.py): segments between opcode-3 events satisfy W_k = b_k·22·b_k with
  b_{k+1} = 12·b_k·42·b_k, b_0 = 12·1120421120; the prediction matches the real opcode word on all of the first 1,000,000
  steps.
* Delay terms for a timeout test (code/delay_terms.py 9 60): S-terms ≤ 9 leaves that reach their normal form after exactly D
  ReplaceAll passes exist for D = 1..15 and 18 (e.g. SSSS: 1; S(SS)SS: 2; SSS(SS)S: 3; S(SS)SSS: 4; S(S(SSS))SS: 5;
  S(SS)(SS)(SS)SS: 18). For D ≤ 5 the head spine tells 'finished' (2) from 'not yet' (≥ 3) at every stage; longer delays
  reach the head-normal shape S a b early and finish inside their arguments, so a reader must open the arguments to see
  completion. So a timeout test 'T ≥ D?' is available at the head only for small D.

## E61 — census coverage by the exact counter theorems, 2026-10-26 (main agent)
Of the 152 counter-type endpoints of the 12-leaf census (111 binary, 40 'OTHER' base-2, 1 nested), the head run reaches a
driver state of a proved theorem within 60,000 steps (after which the theorem's symbolic driver determines the run):
Theorem BC (C1(k)) — 21 binary counters (code/census_coverage.py); the BC2 scheme (top three R′(M) with
M = (S L)(L (S L)); base cases L_0, L_1 return R′(x·y) on generic arguments, checked per term; the BC2 inductive step and
driver are base-independent) — 39 (17 binary + 22 OTHER; code/bc2_general.py). Total 60 of 152 runs now PROVED exact
(modulo the per-term transient and base checks, which are concrete). 2 binary counters show the BC2 scheme with a base
that returns a different form; the remaining 92 (mostly binary counters, 18 OTHER, the nested counter) follow other
schemes — the obvious next family to classify for R″ coverage.
* E61 update: the BC2 symbolic call step and driver go through unchanged with the variant return form
  R″(Z) = [Z(SZ), SS·(Z(SZ)), (SZ)(Z(SZ))] (code/bc2_variant.py: traces 1 2 [call j−1] 4 2 [resume j−1] and
  3 [resume k] 2 2 [resume k]). Accepting R′ or R″ (code/bc2_general.py, base cases checked per term: levels 0/1 take 6/14
  or 7/16 steps), the BC2 scheme covers 39 + 24 = 63 census counter endpoints; with Theorem BC's 21, **84 of 152** are
  proved exact. Uncovered: 49 binary counters (3 of them with the BC2 shape but a base returning another form), 18 OTHER,
  the nested counter. Other families seen by code/level_finder.py: BC-like returns [Z, SS·Z, S(SS(SS)Z)] with
  T_{k+1} = 2T_k + 10 (SSS(S(SS))S(SS(SS))), and a BC2-size family with return [Z(SZ)(SZ(Z(SZ))), …] (SSS(S(S(S(SS))))SS).

## E62 — automatic proofs over the census, 2026-10-26 (main agent)
code/auto_prover.py on all 152 counter-type endpoints of data/lo_census2_12.tsv (code/census_auto.py, one process per term,
2-minute limit; data/census_auto.txt, data/census_auto.log): PROVED with passing event-time cross-check — 111 of 111
binary counters, 33 of 40 OTHER; 'resume pattern unsafe' — 2 OTHER; 'no level family' — 5 OTHER, 1 nested counter.
Validation: the prover re-derives the hand proofs of Theorems BC and BC2 and of the BC2 variant (same traces).
Performance: memoised level containment and a 30,000-step cap on generic runs (5 s for three terms).

## E63 — towards the non-counter census classes, 2026-10-26 (main agent)
All 18,326 distinct hnf-free endpoints of terms ≤ 12 leaves regenerated (code/endpoints_all.py → data/endpoints_12.txt;
18,174 of them are not among the 152 counter-type endpoints of E56/E62).
* Exact recurrence (code/periodic_prover.py: the touched part of a checkpoint stack reappears on top ⇒ periodic forever):
  0 of the first 600 endpoints are eventually periodic in this strict sense — the 'bounded/linear' class consists of
  linear-growth processes, not exact cycles.
* Automatic prover generalised (code/auto_prover.py): linear level families (T_{m+1} = T_m + c) allowed, and return forms
  may use the two halves x, y of the product Z = x·y. On a random sample of 150 non-counter endpoints
  (code/sample_auto.py): 17 PROVED (with cross-check), 39 with the call lemma derived but no driver configuration found
  (linear schemes present their cycle differently), 75 with no call family (flat 'comb' iterators — they need the
  flat-iterator lemma rather than calls), 11 resume pattern not computable, 2 no scheme, 2 driver not derived,
  4 timeouts. So about 11% of the non-counter endpoints are proved by the current machinery; extending driver discovery
  to linear schemes and adding flat-iterator macros are the next steps towards 'R″ for every head run ≤ 12 leaves'.
* E63 update (driver discovery for linear schemes): the template fallback and return forms that depend only on y fixed
  the 'driver configuration not found' cases — the cycle state of a linear scheme is the return state R(·, L_k) at a
  macro boundary (its 'first appearance' of L_{k+1} lies inside a call macro: checked step by step on S(SS)S(SSS)(SSS)S,
  no soundness issue). Random sample of 150 non-counter endpoints (data/sample_auto_150.txt): 59 PROVED, all 59 with a
  passing event-time cross-check (≈ 39%); 75 no level family (flat comb iterators), 10 resume pattern not computable,
  2 no scheme, 4 timeouts. Counter census unchanged: 144 of 152 PROVED with cross-check (no regression).
  Estimated overall: roughly 40% of the 18,326 hnf-free head runs of terms ≤ 12 leaves are proved exact (morphic) by the
  automatic prover; the main remaining class is the flat comb iterators (≈ half of the non-counter runs).
* The 'no level family' class (≈ half of the non-counter endpoints; code/comb_probe.py on SS(SSS)S(SS)SSS,
  S(S(S(SS))S)(SSS)(SS), SS(S(SS))(SS)SS(S(SS)), S(SSS)S(SSS)): bounded spine (maximal opcode 3–5, reached within the
  first 15 steps), list length growing linearly (≈ 0.37–0.5 per step), front elements growing internally without forming
  a nested call family. These are linear counters processing a growing structure element by element; proving them needs
  a parametric iteration lemma (in the spirit of the flat iterator S·S^n·B·S → S·S^{n−2}·B·S of R31) rather than calls.
* Comb runs are single counters (code/defects.py, code/comb_exact.py, 60,000 steps): their opcode words are locally
  periodic with sparse defects whose spacing grows by exactly one period block per cycle, and after a prefix they have the
  exact form D·B^m·D·B^{m+1}·D·B^{m+2}⋯ with fixed words D, B — SS(SSS)S(SS)SSS: B = 30023003, D = 2500103002,
  m = 61, 62, …, 119; S(S(S(SS))S)(SSS)(SS): B = 1021041040, D = 102104103030; SS(S(SS))(SS)SS(S(SS)): B = 202203,
  D = 2310202; S(SSS)S(SSS): B = 203202 with a separator containing one extra block (counts 70, 71, …). Such words are
  morphic (σ(t) = t·B), so R″ holds for these runs on the window (COMPUTATIONALLY CERTIFIED there). The classifier had
  put them in 'bounded/linear'; their 'no level family' status is because the counter is a block count, not a nest of
  calls. A proof engine for this class needs a parametric inner-loop lemma (one B block per element of a growing
  structure) — the analogue of the call lemma for linear growth.

## E64 — call prover + comb prover on the census sample, 2026-10-26 (main agent)
Same random sample of 150 non-counter endpoints (seed 1; code/sample_comb.py, data/sample_comb_150.txt): proved by the
call-based prover 59, additionally by the comb prover 22, neither 69 — 81/150 ≈ 54%, every proof with a passing
cross-check. Comb-prover verdicts on the sample: PROVED 22, front not constant at block starts 85 (mostly call-type runs),
layer not constant 18, block lemma fails 9, second element not a layer 6, driver not derived 5, no long block runs 3,
cycle starts not combs over one base 2. With 144/152 counters, roughly half of all 18,326 hnf-free head runs of terms
≤ 12 leaves are now proved exact (morphic).

## E65 — the loop prover on the rest of the census sample, 2026-10-26 (main agent)
The 69 sampled endpoints that neither the call prover nor the comb prover proves (code/sample_neither.py →
data/sample_neither_150.tsv) were run through code/loop_prover.py (code/sample_loop.py → data/sample_loop_150.tsv):
PROVED 63 (every one with a complete instance cross-check, 50–158 checks each), no growing loop cycle 3, no pattern 2,
unknown rest reached 1. Versions: right combs only, one loop variable — 51; plus loops carrying the variable in several
places — 61; plus context combs F^m(X) with several holes (linked lists whose links refer to the next link twice) — 63.
Totals on the sample: 59 (call) + 22 (comb) + 63 (loop) = 144/150 = 96% proved exact; with 144/152 counters, an estimated
≈ 96% of all 18,326 hnf-free endpoints of terms ≤ 12 leaves (sampling error about ±2%). Unproved in the sample:
S(S(SS)SS)(S(SS)S)SS (exact doubling, gaps g′ = 2g + 66), SSS(S(SS(SS)SS))SS (two interleaved progressions),
SS(SSS(SS))(S(SS))SS (no growing loop cycle), SS(SS)S(S(SS))S(SS)S, S(S(S(SS)S)(S(SS)))(SS)S (no pattern),
SSSS(SS(SS)(SS))(SS) (unknown rest reached).
Also observed: the two census endpoints with unbounded opcodes (S(SS)S(S(S(S(SSS))S))S, S(SS)S(S(S(SS(SS))S))S) reach
opcode m for the first time at step 1.5m³ + m² − 56.5m + 200 exactly (m = 4..51 checked for the first), with front
spines whose elements roughly double in size — a nested (two-level) loop, still to be proved.

## E66 — call prover re-run with strong numerical tests, 2026-10-26 (main agent)
code/auto_prover.py after two changes (PROOF.md 'Automatic exact-structure proofs', correction paragraph): level chains
found as longest containment chains with increasing call times (plus the original greedy chain), and strong_check
replacing the one-gap cross-check. Re-run on all 152 counter-type endpoints (code/census_auto.py → data/census_auto.txt,
data/census_auto.log): PROVED 145 — all 111 binary counters and 34 of 40 'OTHER' (one more than before:
SSS(S(SS))S(SSS(SS)), two interleaved level families) — every proof passing 17–23 independent checks (call-time
recursion on the concrete levels + every driver-event gap in the first 400,000 steps); unproved: 2 'resume pattern
unsafe' (SSS(S(SS))S(SS(SS)), SSS(S(SS))S(SS(SS))S), 1 'no scheme' (SSS(S(S(SS)(SS)(SS)))S), 1 timeout and 3 'no level
family' — the countdown/cubic runs S(SS)S(S(S(SSS)(SS)))S, S(SS)S(S(S(SSSS)S))S, S(SS)S(S(S(S(SSS))S))S,
S(SS)S(S(S(SS(SS))S))S, whose epoch m reads (m−1) m (m−2) m ⋯ m 4 m m m in the large opcodes (fronts are lists of m
entries built from earlier fronts' entries; proving them needs graded list segments and nested induction — not built).
The earlier statement 'each proof with a passing cross-check' (E62) was true but referred to a single gap per term.

## E67 — all three provers on the census sample: 150/150, 2026-10-26 (main agent)
code/sample_union.py runs, per sampled non-counter endpoint (same random 150 as E62–E65, seed 1), the call prover (with the
strong numerical test of E66), then the comb prover, then the loop prover (current version: context combs, coupled
recurrences, up to 24 loops per cycle, several candidate block lengths); a proof counts only if it is PROVED and every
numerical cross-check passes. Result (data/sample_union_150.tsv): **150 of 150 proved exact** — call prover 62, comb
prover 22, loop prover 66. With 0 failures in 150 random draws, the fraction of the 18,174 non-counter endpoints without
such a certificate is below 2% with 95% confidence (rule of three); with 145/152 counters, an estimated ≥ 98% of all
18,326 hnf-free endpoints of terms ≤ 12 leaves have exact, morphic head runs. The full census was not run (it would be an
enormous census; the user excluded those). Loop-prover changes since E65 that mattered: coupled recurrences (an element
built from another element's comb, found by a second anti-unification pass with a family lookup), contexts > 5,000 nodes
rejected, several candidate block lengths, the last (truncated) phase ignored, up to 24 loops per cycle. Examples newly
proved: SS(SSS(SS))(S(SS))SS (15 loops per cycle, 5n + 86, 95/95), SS(SS)S(S(SS))S(SS)S (7 loops, 2n + 44, 150/150),
SSS(S(SS(SS)SS))SS (7 loops, 21n + 99), S(S(S(SS)S)(S(SS)))(SS)S (sizes ×5 per cycle, 6n + 82, 87/87),
SSSS(SS(SS)(SS))(SS) (32n + 76, 41/41).

## E68 — beyond the census: endpoints of random 13–16-leaf terms, 2026-10-26 (main agent)
code/sample_large.py: uniformly random S-terms with 13–16 leaves (Rémy's algorithm), followed leftmost-outermost through
their Böhm trees to an hnf-free endpoint exactly as in the census; the first 100 distinct endpoints (from 145 random
terms; data/sample_large_13_16_firstrun.tsv). Re-run with the current provers in parallel (code/sample_large_par.py →
data/sample_large_13_16.tsv; call → comb → loop prover, 120 s each, a proof counts only with complete numerical
cross-checks): **100 of 100 proved exact** (call 45, loop 38, comb 17). Unproved: none. So the three mechanisms (calls, combs/loops,
context combs) cover endpoints of larger terms at the same rate as the 12-leaf census — evidence (not proof) that
Conjecture R″ does not break down just above the census size. (First run, with older prover versions and the weak
call-prover check: 95/100.)

## E69 — whole-list certificates for loop runs (Corollary LP′), 2026-10-26 (main agent)
The loop prover now runs a residue pass after each proof (same trajectory, pushes kept as graded segments, only the part
below the anchor window left unknown) and tests the resulting description of the whole list — M(n) ++ R(n−1) ++ ⋯ ++
B(n_s) — on the first 30 list entries at every later anchor in 60,000 steps. code/wholelist_check.py on every term
certified by the comb or loop prover in the two samples: whole-list certificates for **143 of 143** (88 from the 12-leaf
census sample, 55 from the 13–16-leaf sample), every 30-entry test passing at every anchor (data/wholelist_check.tsv). For
these terms R″_{k,d} holds for every window size k (Corollary LP′), as Proposition UB needs for bounded-time detectors.
Not yet extended: the call prover (62 census-sample terms, 45 larger, 145 counters keep R″_{3,d} only). Its calls leave
residues that grow like the call times — for SSS(SS)S(SS(SS)) the list below a level-j call's return form has 1, 2, 9,
23, 51, 107, 219, 443 items (r_j = 2 r_{j−1} + 5): a recursive list grammar, to be handled with recursive residue items.

## E70 — whole-list certificates for call runs (Corollary CA′), 2026-10-26 (main agent)
code/call_residue.py replays every call-prover derivation exactly (CALL leaves RES, RESUME leaves REM — the remainder
barrier-checked, symbolically for the inductive levels and with fresh atoms for the base levels — and the driver leaves D)
and tests the resulting whole-list description at every driver event in 300,000 steps (first 30 entries).
code/wholelist_calls.py on every call-certified term: counters 145/145, census sample
62/62, 13–16-leaf sample 45/45 certified
(data/wholelist_calls.tsv). Not certified: none. Together with E69 (all 143 comb/loop-certified terms), every proved
run of both samples and every proved counter now has a whole-list certificate: R″_{k,d} for every window size, which is
what Proposition UB needs for detectors that halt in bounded time on head-first strings.

## E71 — RESUME by the barrier criterion: two more counters; the five left, 2026-10-26 (main agent)
The call prover rejected two counters because a RESUME pattern failed its head test (every item below the resume state's
top three headed by an argument). The exact criterion used for whole-list certificates — the remainder of the call, run
from the resume state's top three with the unknown rest directly below (inner call by CALL, resumes only at strictly
lower levels), returns R(x·y) without reading below its top three; symbolic for the inductive levels, concrete with fresh
atoms for the base levels (code/auto_prover.py, concrete_remainder_barrier) — holds for both. Now PROVED with strong
tests: SSS(S(SS))S(SS(SS)) and SSS(S(SS))S(SS(SS))S (18/18 each), both with whole-list certificates (9/9 events).
Counters: **147 of 152**. The five left all have nested two-parameter structure: SSS(S(S(SS)(SS)(SS)))S has level groups
of 3, 4, 5, … members whose return forms change with the level (call times 68, 152, 324, 672, 1372, …, ≈ 2t + 16 across
groups, +2 within a group) — a call recursion whose return form carries a growing comb; S(SS)S(S(S(SSS)(SS)))S,
S(SS)S(S(S(SSSS)S))S, S(SS)S(S(S(S(SSS))S))S, S(SS)S(S(S(SS(SS))S))S are the countdown runs (epoch m: (m−1) m (m−2) m ⋯
m 4 m m m; cubic schedule). Both need parametric return forms / graded spine segments with nested induction.

## E72 — hunt for new mechanisms among 17–24-leaf terms, 2026-10-26 (main agent)
code/sample_hunt.py: 236 uniformly random terms with 17–24 leaves, followed leftmost-outermost to their hnf-free endpoints;
200 distinct endpoints (median 19 leaves, up to 58; only 22 of them are 12-leaf census endpoints), each given to the loop,
comb and call provers (in that order, 16 in parallel; data/sample_hunt_17_24.tsv). Proved: loop prover 196, call prover
3; one endpoint, S(S(S(SS))(S(S(S(S(S(SS)(SS(SS)S)))S)))S)SSS, was left — an ordinary single-loop run (D·B^n·D·B^{n+1}⋯)
whose block is 70 steps long, beyond the prover's 39-step block search and 64-step loop detection. With block lengths up
to 160 (searched only when no short block works) and loop detection up to 170 steps back it is PROVED (cycle 70n + 254,
27/27 cross-checks). So **200 of 200** endpoints are proved exact, and code/wholelist_hunt.py gives every one of them a
whole-list certificate (data/wholelist_hunt_17_24.tsv). At these sizes loop runs dominate (196 of 200). No candidate for
a new mechanism or a non-morphic run turned up.

## E73 — hunt among 25–40-leaf terms: square nested loops, 2026-10-26 (main agent)
code/sample_hunt.py 25 40 150 11 8: 150 distinct endpoints from 153 random terms (median 29 leaves, up to 96;
data/sample_hunt_25_40.tsv): loop prover 145, call prover 2, unproved 3. The three: S(S(S(S(SS)S))(SS(SSS(S(SS(S(SSS)
(S(SS)SS)))))))(SS)SSSSS(SS) — marks at gaps 39, 48, 252, 832, 2572, 7792, 23452, 70432 (g′ = 3g + 76 from 832 on: a
base-3 call recursion the call prover's family search misses); S(S(SS))S(S(S(SS))S)(S(S(SS))SS(SS)) and
S(SSSS)SS(S(S(S(SSSS)(S(SS)))(SS(S(SS)S(SS))(SS))))(SS)S(SS(SS)) — **square nested loops**: in the first, round m consists
of a mark gap of 9, one block of length 12m + 19 and then m identical blocks of length 12m + 23 (checked identical as
opcode words for rounds with 5–10 marks), each block X·Q^{m+c}·Y with Q = 411011020401. So the opcode word has the form
∏_m (X Q^{m+c} Y)^{m+c′} Z — the inner count equals the repetition count, a two-parameter structure. Whether such words
are morphic is in doubt (PROOF.md, 'Weakening the bridge'); they are effectively profinitely ultimately periodic, which is
what Proposition UB needs (Carton–Thomas). Not yet proved: needs nested induction.

## E74 — nested-loop prover: the square runs proved, 2026-10-26 (main agent)
code/nest_prover.py (Theorem NL): exact macros with symbolic segments, nested block lemmas (inner loop macros inside a
block, polynomial block length), loop detection across macros, polynomial step counts, two-pass soundness, rounds found as
driver occurrences between which the number of loop phases grows by one. PROVED: both square runs of E73 —
S(S(SS))S(S(S(SS))S)(S(S(SS))SS(SS)) (round 12n² + 11n + 5, 18/18 instance checks) and
S(SSSS)SS(S(S(S(SSSS)(S(SS)))(SS(S(SS)S(SS))(SS))))(SS)S(SS(SS)) (4n² + 11n + 5, 26/26); it re-proves the regular run
S(S(SS)SS)S(SS) (10n + 30, 132/132). Not proved: the countdown runs (S(SS)S(S(S(SSS)(SS)))S: no comb pattern at round
starts; S(SS)S(S(S(SSSS)S))S: no round structure — unbounded opcodes) — they need a second symbolic variable.

## E75 — strict parallel robustness is rare, 2026-10-26 (main agent)
By Lemma PH a parallel (ReplaceAll) pass is one head step plus one pass inside every list element below the first three,
so if all those elements are normal forms at every step, the parallel evolution equals the head run step for step and
every leftmost-outermost certificate would transfer. code/robust_scan.py 20000 on 602 runs (census sample 150, counters
152, 13–16 sample 100, 17–24 sample 200): only **1** satisfies this on its first 20,000 steps; in all others a non-normal
element sits below the first three within the first 100 steps. (The earlier 'parallel-robust' counters, e.g. K0, satisfy
the transfer lemma's weaker condition — no *relevant* waiting slot is non-normal — which preserves the control flow but
not the list contents a bounded-window detector reads.) So the leftmost-outermost certificates do not transfer to parallel
evaluation as they stand: gap (4) of the gap map needs its own theory (waiting elements evolve by their own parallel
evolutions while they wait).

## E76 — hunt among 40–80-leaf terms; parallel evaluation keeps infinite processes waiting, 2026-10-26 (main agent)
code/sample_hunt.py 40 80 100 23 12: 100 distinct endpoints from 101 random terms (median 55 leaves, up to 213;
data/sample_hunt_40_80.tsv): loop prover 95, call prover 2; of the 3 left, the nested-loop prover proves one (a square run,
round 4n² + 11n + 5, 26/26) — **98 of 100 proved exact**. The two others look regular but are not yet certified: a binary
counter (blocks B² separated by runs of '21' of lengths following a ruler-like sequence; the call prover derives the call
step but not the driver) and a linear-growth loop (rare opcodes recur at gaps 68, 76, 84, …, 1780, i.e. +8 per cycle; the
pattern inference finds no comb pattern). No candidate for a non-regular run in any hunt so far (12–80 leaves).
Parallel evaluation (gap 4): in 301 of the 302 census and counter runs some element waiting below the first three has no
normal form (code/robust_scan.py + lo_bt.normalises on the first 1,500 steps), so under parallel evaluation infinite
evolutions run *inside* the list while the head machine proceeds — the parallel order is a hierarchy of nested
evolutions, not a delayed copy of the head run. Any theory of gap (4) has to handle that.

## E77 — soundness audit of the nested-loop prover: square-run certificates withdrawn, 2026-10-26 (main agent)
Audit finding: code/nest_prover.py ran inner block lemmas (loop_prover.block_lemma / simple_macro) inside nested block
lemmas whose states already contain the outer opaque atom O (= −1), and the inner lemmas used the same atom for their own
unknown T. The engine never opens either, but the final comparison cannot tell which −1 is which, so an inner block that
moved O into T's place (and T into O's) would wrongly pass. Fix: a distinct opaque atom per nesting depth (−1, −2, −3).
After the fix the two square runs of E74 are NOT proved (cycle lemma: token unfolded too often) — their E74 certificates
are withdrawn; their structure stays EXPERIMENTALLY SUPPORTED by the passing instance checks. The regular run
S(S(SS)SS)S(SS) is still proved by nest_prover; loop_prover itself is unaffected (its block lemmas only see top-level states,
which contain no opaque atom).
Follow-up (same day): the failure after the first fix came from the residue check — the inner loop's pushed segment
really does mention the outer variable, which the shared atom had renamed to the inner loop variable (a genuine
mislabelling, not just a theoretical gap). Corrected design: per-depth opaque atoms (−1, −2, −3) and per-depth loop
variables (−50, −60, −70); segments ("G", P, F, X, b, w) carry their own variable w; substitution reaches into nested
segments without touching their own variables. With it both square runs are **re-proved**: 12n² + 11n + 5 (18/18) and
4n² + 11n + 5 (26/26); the regular run S(S(SS)SS)S(SS) still 10n + 30 (132/132). loop_prover.py, call_residue.py and
auto_prover.py were checked for the same kind of conflation: their block lemmas and macros only ever see states without
another lemma's unknowns (loop prover: top-level states; call prover: x, y bound per call, inner calls summarised by
macros; call_residue expands each RES/REM item in its own environment).

## E78 — RESUME made optional when its barrier fails (soundness hardening), 2026-10-26 (main agent)
The call prover's RESUME macro (resume a level-j call at its continuation) is now available only when the concrete and
symbolic barrier criterion of E71 holds; the earlier 'head test' is gone (insufficient in principle). First version:
a failed barrier aborted the proof ('resume pattern unsafe'), which lost SSS(S(SS))S(SSS(SS)) although its derivation
never uses RESUME. Final rule (code/auto_prover.py): a failed barrier only withdraws the macro; derivations then run
without it and fail only if they need it. Re-runs: counters **147/152** (unchanged; the five left are the four countdown
runs and the 'no scheme' run), census sample **150/150** (call prover 65, loop prover 63, comb prover 22 — three terms
moved from the loop prover to the call prover, and call_residue.py gives all three whole-list certificates, 29/29
events, no RESUME used); code/verify_all.py 31/31 PASS.

## E79 — certified opcode words of the square runs; Theorem NM (morphic R″ refuted), 2026-10-26 (main agent)
code/nest_prover.py now records, as bookkeeping on the same symbolic runs, the opcode of every symbolic step and every
loop macro (blocks carry their own recorded words; a tuple subclass Mac keeps the macro interface unchanged), and
code/loop_prover.py's engine records its step opcodes. code/nest_words.py reads off the cycle word C(n):
t_1 = S(S(SS))S(S(S(SS))S)(S(S(SS))SS(SS)): C(n) = Q^{n−2} (E Q^{n−1})^{n−1} G Q (n ≥ 19, from step 27,311);
t_2 (33 leaves): C(n) = q^{n−2} D (F q^{n−1} D)^{n−1} H q (n ≥ 27, from step 28,846) — see PROOF.md for the words.
Bookkeeping tests: |C(n)| = the certified cycle length, and the expansions of 14 and 12 consecutive cycles equal the
concrete opcode words (115,969 and 55,622 steps). Marker test (marker E resp. F): n − 1 occurrences per cycle n, and the
factors between consecutive markers are confined to single cycles (19 distinct factors over 10 cycles of each run).
With Lemma S (PROOF.md) this proves Theorem NM: both opcode words, hence their (k, d)-window words for d ≥ 6, are not
morphic — Conjecture R″ in its morphic form is false; R″_PUP (all that Proposition UB needs) holds for them.
Side observation: the countdown run S(SS)S(S(S(SSS)(SS)))S has bounded opcodes (max 3); its epoch m reads
3 (03)^m 0213 (03)^{m−1} 0213 ⋯ (03)^1 0213 021213021, a countdown word (Lemma NW). *Correction (E83): this holds for
that run only — the other three countdown runs reach opcodes 46–51 within 200,000 steps (unbounded, as E71 said); an
earlier version of this note claimed bounded opcodes for all four.* Their states hold a growing list of
frames (frame j: one large item and j items of nearly equal size; sizes grow by φ² ≈ 2.618 per epoch), so a prover
needs nested graded segments and loops that walk them — not built.

## E80 — unique-redex terms; leftmost-innermost evolution; comb-prover audit, 2026-10-26 (main agent)
(a) Unique-redex terms (code/unique_redex.py: all elements normal forms and the second element S or S z at every step,
so the head redex is the only redex): none with ≤ 9 leaves; 2, 3, 10, 26, 68 terms with 10, 11, 12, 13, 14 leaves keep a
unique redex for 3,000–5,000 steps. Every one of these 109 runs is a linear counter (opcode word, runs of 2 collapsed:
…1202 1202… for 107 of them, …11220 2^n… for the other two, S(SSS)S(S(S(S(S(SSS)S)))S) and S(S(SSS))(S(S(S(S(SSS)S))))S).
S(S(SSS)S)S(S(S(S(SSS)S)S)) keeps a unique redex for 2,000,000 steps (list length about 2·10^6). Theorem UR (PROOF.md)
proves the property for ever for t_0 = S(SSS)S(S(SSS)S); code/unique_redex_t0.py checks the proof's claims on 300,000
steps (1,533 Φ-states). Both 10-leaf terms are also call-prover certified with whole-list certificates (389/389, 29/29).
(b) Leftmost-innermost (code/li_explore.py, li_path.py): all 43 non-normalising terms with ≤ 8 leaves descend for ever in
3,000-step runs (the depth of the contracted redex grows; the outside freezes). S(SSS)S(SSS): the frozen path always
enters the third argument, frozen siblings in groups of j + 1 levels with sizes ≈ 4j (nested-loop pattern).
SSS(SS)S(SS(SS)) (the binary counter): descends with exponentially growing normal forms (size cap 2·10^6 reached after
162 steps) — under LI it is not a counter. code/cbv_robust.py: of the 602 head runs of the samples and the counters, only
S(S(SSS)S)S(S(S(S(SSS)S)S)) keeps its first three elements normal (for 200,000 steps); all others fail within 20 steps.
(c) Comb-prover audit (code/comb_prover.py): distinct atoms for T, E′ and the rest (no conflation), opaque heads never
opened, the unknown rest barred from the top three in the driver. One gap: with a comb-shaped third element the block
lemma needs at least one layer in E at the first certified cycle, which was not checked; now it is (the first cycle used
must have it). All 22 comb-proved sample terms are still PROVED with full cross-checks.
(d) Bookkeeping: hc.size keeps a global memo, which goes stale if the term tables are reset; li_explore.py now uses its
own per-term memo (no other script resets the tables and uses hc.size). The first li_explore run (≤ 8 leaves) did not
reset the tables, so its numbers stand.

## E81 — root call-by-value census; call-prover driver fallback, 2026-10-26 (main agent)
(a) code/cbv_root.py runs leftmost-innermost at the root as a machine on the list: before each contraction the first three
elements are normalised (memoised leftmost-outermost normaliser, 20,000 head steps per normalisation, node cap); an element
without a normal form within the budget counts as descent. Terms whose root keeps contracting for 2,000 contractions:
**1, 13, 40 with 9, 10, 11 leaves** (all terms enumerated; 9 leaves: S(S(SSS))(SS)(SS), checked with exact LI: 5,786 of
6,000 steps at the root, depth ≤ 3). Most of them normalise arguments on the way (about 62 normalisations per 2,000
contractions — the spacing grows by one, as in a linear counter); 2 of the 13 and 5 of the 40 never needed a
normalisation (the unique-redex terms of E80 and relatives). Descents within the budget: 908 (10 leaves), 3,941 (11).
A first version of the normaliser rebuilt the whole spine at each head step and grew to 16 GB on one term; it was stopped
and replaced by a head machine on the spine list with a node cap (no results from the stopped run were used).
(b) Call prover: when the event-based driver derivation fails, the prover now also tries the template driver (it used it
only when no events were found). The E76 binary counter S(SS(SSS(S(SS))))(…)(SSS) is now **PROVED**: call step
'1 2 [call −1] 4 2 [resume −1]' (j ≥ 2), driver '[resume +1] 2 2 [resume +1] 3', strong cross-check 15/15; whole-list
certificate (code/call_residue.py) 7/7 events. The 40–80-leaf hunt is now **99 of 100** proved; the one left is the
linear loop whose list front is rebuilt every cycle (every top element is a new term at each cycle start, so the loop
count is not a comb token found by anti-unifying three states — needs a new kind of pattern inference). Terms proved
before are unaffected (the change only acts after the event driver has failed).

## E82 — scheme inference tolerates a misdetected last level; the base-3 call run proved, 2026-10-26 (main agent)
The call prover required L_{k+1} = F[L_k] for every consecutive pair of the observed level chain. For the E73 base-3 run
S(S(S(S(SS)S))(SS(SSS(S(SS(S(SSS)(S(SS)SS)))))))(SS)SSSSS(SS) the first five members (sizes 57, 141, 309, 645, 1317)
satisfy one context recursion and only the last observed member (2658, near the end of the sampled run) does not.
code/auto_prover.py now drops trailing members that break the recursion (keeping at least three that fit); every level is
defined by the scheme itself, and the call lemma, driver derivation and strong checks do not use the dropped members, so
soundness is unchanged; terms whose full chain fits behave exactly as before. Result: **PROVED** — call step (j ≥ 1) with
three inner calls '… [call −1] … [call −1] … [call −1]' (an exact base-3 recursion), driver with same-level calls and one
'[call +1]', strong cross-check 10/10; whole-list certificate 4/4 events (call-step residue 15 items, driver residue 39).
The 25–40-leaf hunt is now **150 of 150** proved. The 12-leaf 'no scheme' counter SSS(S(S(SS)(SS)(SS)))S is not affected:
its level chains (3, 4, 5, … members) have contexts that shrink along each chain (sizes 2127, 818, 321, 139), i.e. the
return form really changes with the level — still open (needs parametric return forms).

## E83 — opcode-word encoding bug (opcodes ≥ 10) fixed; the 40–80-leaf hunt complete, 2026-10-26 (main agent)
Bug: code/loop_prover.py, nest_prover.py and comb_prover.py built the opcode word as "".join(map(str, ops)), so an
opcode ≥ 10 took two characters and every later string position drifted from its step number; cycle starts found in the
string were then used as step numbers for snapshots. Effect: completeness only — a certificate is checked against the
concrete state at the step it actually uses (transient instance check) and its cycle lemma is symbolic, so a misaligned
start can make a proof fail but cannot produce a false one. Fix: one character per step, chr(48 + opcode) ('0'–'9'
unchanged, ':' for 10, ';' for 11, …; helper loop_prover.opword). Diagnosis came from the last unproved hunt run (the
'rebuilt list' loop of E81): its snapshots at the claimed loop starts did not have opcode 0 at the front, contradicting
the opcode word. That loop is now **PROVED** by the unchanged loop prover — block 00230033, cycle length 8·n + 68,
cross-check 76/76, whole-list certificate 74/74 anchors; the 'rebuilt list' explanation in E81 was a misdiagnosis.
The **40–80-leaf hunt is now 100 of 100** proved. Scan of every sampled run (census sample, 13–16, 17–24, 25–40, 40–80):
12 runs have an opcode ≥ 10 within 200,000 steps; the 10 of them proved before are all re-proved with the fixed
encoding (full cross-checks and whole-list certificates), the other 2 are the two newly proved runs (E81, this entry).
Census counters: the 147 proved ones are call-prover proofs, which use no opcode string, so they are unaffected; three of
the unproved countdown counters (S(SS)S(S(S(S(SSS))S))S, S(SS)S(S(S(SS(SS))S))S, S(SS)S(S(S(SSSS)S))S) reach opcodes
46–51 (an earlier draft of this entry said all counters stay ≤ 9 — unchecked and wrong).
Countdown runs (side result of the diagnosis): at consecutive epoch starts each top element consists of about m + 10
new nodes around about m + 10 subterms of the previous epoch's elements (both counts growing by one per epoch; the
largest reused piece ≈ 0.4 of the element) — combs of length ~m over the previous epoch's pieces, a level recursion
whose context is itself a growing comb (neither the call nor the loop prover represents it).

## E84 — audit of the loop prover's cycle lemma; residue-pass anchor check, 2026-10-26 (main agent)
Checked in code/loop_prover.py: (i) after every loop macro the main pass keeps only the macro window A(X) and replaces
everything below it by unknown junk, so the cycle from an anchor M(n) never reads below M(n)'s window — M(n) ++ r →*
M(n+1) ++ r′ for every r; (ii) block lemmas run with junk directly below their window, and the macro's state is A(T(F, X, b))
by construction (simple macros substitute the token itself; abstracted windows satisfy A(T(F, X, bmin)) = current window
because F^{b′−bmin}(T(F, X, bmin)) folds to T(F, X, b′)); (iii) closure compares the first h₁ elements with the shifted
anchor window, and the j extra blocks need n + b ≥ j, implied by n + b₁ ≥ 0; (iv) every token count n + b used by macros
or patterns enters n₀, and the first certified cycle has n ≥ n₀ with an exact instance check of the window; (v) folding
with comb families from other terms or attempts can only fold their own tokens; a change of the family set between two
pattern constructions can only make an equality test fail (completeness), never succeed wrongly. One gap, affecting only
the whole-list certificates (Corollary LP′): the residue pass was required to reach the same cycle length as the proof
but not the same closing anchor (the nested prover checks both); now it must close at the same anchor. Theorem NM detail
re-checked: both square runs have opcodes ≤ 5 in their transients as well (27,311 and 28,846 steps), so 'd ≥ 6' holds as
stated.
Re-run after the anchor check (code/wholelist_check.py, wholelist_hunt.py): 140 loop/comb-certified sample terms keep
their whole-list certificates (the 3 others of the earlier 143 are the terms that moved to the call prover in E78, which
have call-prover whole-list certificates); the 17–24-leaf hunt keeps 200/200; code/verify_all.py 33/33 PASS.

## E85 — hunt among 80–160-leaf terms; cycles with loops of different blocks, 2026-10-26 (main agent)
code/sample_hunt.py 80 160 100 31 10 (now with the nested prover as a fourth prover, 300 s): 100 distinct endpoints
from 100 random terms with 80–160 leaves (data/sample_hunt_80_160.tsv): loop prover 97, call prover 2, one left. The one
left (159 leaves) has a cycle with TWO DIFFERENT loop blocks (01204 and 0402022, each run n times; cycle length grows by
5 + 7 = 12 per cycle). The loop prover's symbolic engine detects loops of any block, but its cycle finder looked for one
repeated block, and the other loop's growing run made every separator different, so no cycle was proposed. New:
loop_prover.find_cycles_marker — cycle starts from a marker symbol occurring q times per cycle whose q-strided gaps grow
by a constant d ≥ 1 (tried only after the block-based candidates fail, so earlier proofs are unchanged). Result:
**PROVED** — marker '3' (4 per cycle), cycle length 12·n + 296, two loop macros, cross-check 67/67, whole-list
certificate 65/65 anchors. **80–160-leaf hunt: 100 of 100 proved.** code/verify_all.py 33/33 PASS.
No new mechanism and no candidate for a non-PUP run at 80–160 leaves.

## E86 — hunt among 160–320-leaf terms, 2026-10-26 (main agent)
code/sample_hunt.py 160 320 100 37 10: 100 distinct endpoints from 100 random terms with 160–320 leaves (endpoint sizes
10–521 leaves, median 218; the 80–160 hunt of E85: 11–269, median 113): **all 100 proved by the loop prover** (with
cross-checks; data/sample_hunt_160_320.tsv). At these sizes every endpoint run is a loop run — no call recursion, no
nested loop, no new mechanism, no candidate for a non-PUP run. Totals over all random hunts (13–320 leaves): 750 of 750
endpoints proved exact.

## E87 — hunt among 320–640-leaf terms; a third square run, 2026-10-26 (main agent)
code/sample_hunt.py 320 640 100 41 10: 100 distinct endpoints (39–1,129 leaves, median 444) from 100 random terms with
320–640 leaves: **all 100 proved** — loop prover 95, call prover 4, nested prover 1 (data/sample_hunt_320_640.tsv). The
nested one (444 leaves) is a third square run, cycle length 5·n² + 11·n + 5; code/nest_words.py gives its certified word
C(n) = Q^{n−2} (E Q^{n−1})^{n−1} G Q (Q = 01204, E = 0120501031020402, G = 012050103102050103102), expansion = concrete run
on 10 cycles, marker test passed (n − 1 markers per cycle, inter-marker factors confined to single cycles), opcodes ≤ 5
from the start. Theorem NM's argument applies (PROOF.md): its opcode word is not morphic. Random hunts now total
850 of 850 endpoints proved (13–640 leaves).

## E88 — the bounded countdown counter proved exactly (Theorem CD), 2026-10-26 (main agent)
Named traces (each new term named once and defined over earlier names) showed that the epoch heads of
S(SS)S(S(S(SSS)(SS)))S are chains through all earlier heads: X_e = Ch(1, e−1) with Ch(k, e) = S S (S X_k) Ch(k+1, e) and
Ch(e, e) = T_e = S (S X_e)(S S (S X_e)); an epoch walks the chains of X_{m−1}, X_{m−2}, …, X_2 (two steps per layer — the
'(03)' blocks — the walk lengths counting down) and builds the next head from the end. code/countdown_proof.py checks the
three lemmas W, E, O and the 10-step base part B symbolically (opaque atoms, junk below), the head identities and epoch
starts concretely (e ≤ 26), the predicted opcode word against 5,382 concrete steps, and the whole list (30 entries) at
23/23 epoch starts; the induction is in PROOF.md (Theorem CD). Epoch m: m² − 3m + 10 steps, word 3·D_{m−4}·0212130212201 —
a countdown word, morphic (Lemma NW). Census counters proved exactly: **148 of 152**. code/verify_all.py now has 34 checks,
34/34 PASS. The three other countdown counters have growing opcodes and heads that are not chains of earlier heads in
the same way (first look) — not done.
First look at the three growing-opcode countdown counters (S(SS)S(S(S(SS(SS))S))S studied): the element opened with
the large opcode m at epoch m has a spine of exactly m arguments (4, 5, …, 15 at steps 15, 80, 161, …, 5255), but no
argument is shared with the previous epoch's widest head — the whole spine is rebuilt each epoch (in the named trace,
long spines such as S n7 n10 n31 n49 n52 are assembled step by step during the epoch). So the closed form is not a
simple 'one more argument' list; the Theorem CD method (named trace → closed form → walk lemmas) needs a different
closed form here. Not done.
Closed form found (named trace, S(SS)S(S(S(SS(SS))S))S, 900 steps; not yet proved): a level family a_0 = S n3 n5 S (n3 =
S (SSS) S, n5 = S n4, n4 = S (S (SSS)(SS)) …), a_{k+1} = S S (S a_k) (S (S a_k)), b_k = S (S a_k); the element opened with the
large opcode at epoch m is E_m = S a_{m−1} b_{m−1} a_{m+1} f_m f_{m−1} ⋯ f_0 with frames f_k = S a_k b_k E_m^{(k+1)}, where
E_m^{(k+1)} is the prefix of E_m's spine up to f_{k+1} — a self-referential list of frames, one per level (the 'pending
frames F_k·Y·Z' of the old notes). A proof would combine call-prover level tokens (a_k) with a frame-walk lemma as in
Theorem CD. The 'no scheme' counter SSS(S(S(SS)(SS)(SS)))S has chain tops Top_{g+1} = S S (S Q_2)(S S (S Q_1)(S S (S Top_1)
(⋯ (S S (S Top_g)(S S (S S D)(S Top_g)))⋯))) (D = SS; Q_1, Q_2 fixed) — again a chain through all earlier tops.
Check (code/countdown2_closed_form.py 12000): the closed form of the widest element E_m holds at every epoch m = 3..15
(steps 307–11,497; the a_k recursion between consecutive frames, b_k = S (S a_k), frames pointing to the spine prefixes).
The epoch dynamics (named trace, epoch m = 4) consists of descents through the levels (a_k opened as S c_{k−1} b_{k−1}),
frame construction, frame walks and a fixed base piece — regular, but more lemmas than Theorem CD needs. Status of this
run: closed form EXPERIMENTALLY SUPPORTED (13 epochs), exact proof not done.
Level-call lemma for S(SS)S(S(S(SS(SS))S))S (code/countdown2_call.py): with a_0 = S(S(SS(SS))S)(S(S(S(SS(SS))S)))S,
a_{k+1} = S S (S a_k)(S (S a_k)), b_k = S (S a_k) and the return form R(Z) = [Z, S (S Z), S S (S Z)(S (S Z))]:
DL [a_k, X, Y] ++ r →⁴ [a_{k−1}, X′, Y X′, X Y] ++ r with X′ = S a_{k−1} b_{k−1} Y (opcodes 3011) and BASE [a_0, X, Y] ++ r
→^20 R(Y) ++ … ++ r (opcodes 32200104010210312201) are checked symbolically (X, Y, a_{k−1} opaque, junk below), so by
induction CALL [a_k, X, Y] ++ r →^{4k+20} R(Y f_{k−1} ⋯ f_0) ++ … ++ r with self-referential frames
f_j = S a_j b_j (Y f_{k−1} ⋯ f_{j+1}) — a call that returns into its second argument with a frame list (not the call
prover's R(x·y) convention, which is why it found no family). CALL matches the concrete run at all 14 epochs tested
(states and opcodes). Macro trace (epoch m = 4): from R(E_m) the epoch runs m phases j = m−1, …, 0: open
S a_j b_j a_{m+1} f_m ⋯ f_0 and call a_j (→ R(a_{m+1} g_{j−1} ⋯ g_0)), then open that and call a_m (→ R(S a_{j−1} b_{j−1}
a_{m+1} f_m h_{m−1} ⋯ h_0)); the last phase builds R(E_{m+1}). Remaining for a proof: the two transition lemmas between
R-states (open + set up the next call), with the list below explicit.

## E89 — two growing-opcode countdown counters proved exactly (Theorem CD2), 2026-10-26 (main agent)
S(SS)S(S(S(SS(SS))S))S and S(SS)S(S(S(SSSS)S))S: a level family a_{k+1} = S S (S a_k)(S (S a_k)) over a per-term base a_0,
a level-call lemma that returns into its second argument with a self-referential frame list (DL + BASE, B = 20 resp. 22
base steps), two transition lemmas (TB, TB0), and an epoch of m phases (a countdown over the frames) — composition in
PROOF.md (Theorem CD2). code/countdown2_proof.py: lemmas symbolic; R(E_3) reached; composed opcode words equal the concrete
runs over 9,328 and 7,995 steps (epochs 3–14 resp. 3–13); whole list 11/11 and 10/10. Epoch lengths 6m² + 47m + 28 and
6m² + 51m + 30. A first epoch-length formula in the script was algebraically wrong (the composed word and the run agreed;
the formula did not) — corrected to 6m² + (2B + 7)m + B + 8. **Census counters proved exactly: 150 of 152.** Left: the
countdown S(SS)S(S(S(S(SSS))S))S (its widest elements are not of this frame form) and the 'no scheme' counter.

## E90 — the last countdown counter proved exactly (Theorem CD3), 2026-10-26 (main agent)
S(SS)S(S(S(S(SSS))S))S: generic level calls (atoms X, Y) return into Y with the same self-referential frame lists as in CD2,
but with level context G(L) = S (S (S L)) (S L (S (S L))), 3-step descents (opcodes 211), a 17-step base, return form
R′(Z) = [Z, G(Z), S Z (S (S Z)) G(Z)], and a final phase with one more call (macro trace of epoch 4). code/countdown3_proof.py:
DL′, TB′, TB0′, BASE symbolic; R′(E_3) reached at step 368; composed opcode word = concrete run over 5,328 steps (epochs
3–12); whole list 9/9; epoch lengths 4.5m² + 42.5m + 44 (286 and 369 for m = 4, 5, as observed). **Census counters proved
exactly: 151 of 152.** Only the 'no scheme' counter SSS(S(S(SS)(SS)(SS)))S remains unproved anywhere (census, samples,
hunts).

## E91 — the 'no scheme' counter: call structure found, base call open, 2026-10-26 (main agent)
SSS(S(S(SS)(SS)(SS)))S (the last unproved census counter). Families (chains) g = 1, 2, …: members L_{g,0} = S S (S S D)(S T_{g−1})
(D = SS; T_0 = Q_1) and L_{g,j+1} = S S (S Y_j) L_{g,j} with layer arguments Y_j = T_{g−1}, …, T_1, Q_1, Q_2 (inner to
outer); the last member is the chain top T_g. Return form of family g (from the call prover's family key):
R_g(Y) = [Y, S T_{g−1} Y, S S (S C)(S S (S S D)(S C))] with C = Ch_g(Y) = S S (S Q_2)(S S (S Q_1)(⋯(S S (S T_{g−1}) Y)⋯)),
the chain of T_{g−1}'s layer arguments plus T_{g−1}, ending in Y — so the return form depends on the family (why the call
prover found 'no scheme'). Layer step = a tail call: [S S (S Y_j) L, X, Y] →² [L, S Y_j L, Y, …], so every family member's
call reduces to the base member's call, whatever the layer arguments are. Open: the base call [L_{g,0}, X, Y] →* R_g(Y),
which walks T_{g−1}'s chain layer by layer (each layer through a sub-procedure using the fixed pieces D D D and
S(S(SDDD))S, creating new layers of the form S S D (S Y) ⋯; trace of g = 3 in the session log). Needed: a per-layer lemma
for that walk, its end, and the driver over the tops.

## E92 — the 'no scheme' counter: family call lemma proved, driver open, 2026-10-26 (main agent)
code/noscheme_lemmas.py (plus the W/Wb checks of the session): every family call of SSS(S(S(SS)(SS)(SS)))S returns R_g(Y).
Structure: a family call is a chain of tail calls (TC, 2 steps per layer) down to the base member B_g = S S (S S D)(S T_{g−1});
its call enters T_{g−1} ([T_{g−1}, Y, S S D (S T_{g−1}) Y] after 3 steps), and Enter(k, P, Q) = [T_k, P, Q] works as a binary
recursion: walk T_k's k+1 layers (W) and its base (Wb) into Enter(k−1, Q, S S D (S T_{k−1}) Q) → R_{k−1}(S S D (S T_{k−1}) Q)
→C1→ Enter(k−1, Q, [T_{k−1}|Q]) → R_{k−1}([T_{k−1}|Q]) →C2→ R_k(Q) (the chain inside R_{k−1}([T_{k−1}|Q]) is the chain of
R_k(Q) by definition); bottom: BASE0 [Q_1, P, Q] →^30 [Q, *, U([Q_2|Q])]. Time e_k = 2e_{k−1} + 2k + 10 — the 'exact doubling'
noted in E71. All local lemmas symbolic. Driver (open): the run calls each top T_g on the next family's first two members,
[T_g, L_{g+1,0}, L_{g+1,1}] (steps 53, 121, 273, 597, …), and the identity U(T_g) = L_{g+1,1} links return forms of one family
to members of the next. Status: call lemma PROVED (computer-checked local lemmas + induction), whole run not yet.

## E93 — the last census counter proved (Theorem NS); all 152 census counters exact, 2026-10-26 (main agent)
SSS(S(S(SS)(SS)(SS)))S: the driver needs no new lemma — Δ_g = R_g(B_g) = [B_g, S T_{g−1} B_g, [T_g|B_{g+1}]] (identity
U(T_g) = [T_g|B_{g+1}]) is itself a base call of family g, which returns R_g([T_g|B_{g+1}]) (E92), and C2 turns that into Δ_{g+1}.
code/noscheme_proof.py: six lemmas symbolic; Δ_1 at step 57 and Δ_2..Δ_10 at the predicted steps (gaps 70, 154, 326, … =
44·2^g − 4g − 14); composed opcode word = concrete run over 44,662 steps; whole list 9/9. **All 152 counter-type runs of the
12-leaf census are now proved exact.**

## E94 — parallel vs head opcode words for loop runs: aborted (memory), 2026-10-26 (main agent)
Attempted: 200 ReplaceAll passes (code/parallel_eval.step_fn) for 20 loop-run terms of the census sample, comparing the
element opened at each pass (Lemma PH) with the head run's opcode word. The process reached 9.8 GB before finishing the
first terms and was stopped (no results kept). Cause: a single pass on a large term creates many new DAG nodes, and the
node cap was only checked between passes. A rerun needs a cap inside the pass function. Not rerun yet. (K0's parallel
robustness for all time remains a hand argument plus a 200,000-step machine check; making it machine-checked would need
a relevance-tracking replay of K0's call-prover derivations.)

## E95 — parallel vs head opcode words, capped inside each pass, 2026-10-26 (main agent)
code/par_vs_head.py 150 1500000 20 (the E94 rerun with the node cap checked inside the pass function): 14 of the 20
loop-run terms finished before the process was stopped by PID at 5.5 GB. Every term was capped, but memory grew from term
to term in one process. Results (data/par_vs_head.txt): the parallel word agrees with the head word for only 3–29 passes
(median 10.5); 11 terms hit the 1.5M-node cap after 66–130 passes (the parallel terms grow super-polynomially: DAG sizes
9, 481, 14,602, 140,732, 869,559, 1,955,653 at passes 0, 40, 80, 120, 160, 180 for S(S(SSSS)SS)SS, code/par_words.py);
3 reached 150 passes. The parallel words looked repetitive. The direct method cannot go further, which led to E96.

## E96 — lazy parallel evaluation: every census-sample parallel run to 20,000 passes, 2026-10-26 (main agent)
code/lazy_par.py (Lemma LZ, PROOF.md): elements carry pending passes and are evolved only when opened; the result is the
exact parallel run's opcode word. *Validation:* lazy = direct (capped ReplaceAll passes) on all 14 E95 terms, on every
pass the direct method reached (68–200 passes per term). For S(S(SSSS)SS)SS, the direct computation needs 1.96M nodes for
181 passes; the lazy machine needs 293. *Census* (code/par_census.py 20000, data/par_census_150.tsv): all 150 terms of
the census sample run 20,000 parallel passes in under a second each (≤ 59k nodes).
* Identical to the head word for all 20,000 passes: 3/150 — SSS(SS)S(S(S(S(SS))S)), S(SS(SSS))S(S(S(SS)))S and
  S(S(SSS)S)S(S(S(S(SSS)S)S)) (the 2,000,000-step unique-redex term of Theorem UR's frequency remark). These are exactly
  the three runs in which no forcing does any work.
* All others diverge within 2–62 passes (the waiting second and third elements are rewritten before the head reaches them).
* The loop prover's cycle finder gives a block or marker cycle candidate for 147/150 parallel words, the same count as
  for the head words. The three without one are the same three call-prover runs (S(S(SS)SS)(S(SS)S)SS,
  SSS(S(S(SS))S)(SSSS), S(SS)SS(S(S(S(S(SS)))))S) in both orders. Largest parallel opcode ≤ 12 except in 3 loop runs.
* Nested evolution is small (code/par_force_stats.py, data/par_force_stats.txt). In 147 terms no single forcing
  executes more than 13 sub-steps. In S(S(SS(SS))(S(SS)S))SS, SS(SS)(S(SS)S)SSSS and SSS(SS)(S(SS)SS)(SS), single
  forcings reach 175–199 sub-steps. The median total over 20,000 passes is 277 sub-steps.
*Reading:* parallel runs are head-machine runs plus small, bounded nested evolutions, and their words look just as regular
as the head words. EXPERIMENTALLY SUPPORTED; per-term exactness needs proofs (E97).

## E97 — the first exact parallel run of a loop term (Theorem PL), 2026-10-26 (main agent)
t = S(S(S(S(SSS)(SSS))))SS: parallel and head words differ from pass 8 on. In the head run, the waiting element
SSS(S(SS)) is opened later and costs extra steps. In the parallel run, it becomes the normal form L L = C_2 one pass after
it starts waiting (L = S(S(SS))). The parallel word is a single growing loop, simpler than the nested head word:
u ∏_{j≥4} 110311031104 (11031104)^{j−3} (200,000 passes inspected; only 1103/1104 blocks after the prefix).
code/par_loop_proof.py proves it (PROOF.md, Theorem PL): lemmas (I) Σ_j →^12 Λ_{j−2} and (II) Λ_i →^8 Λ_{i−1} on
the lazy machine with symbolic normal-form atoms for the comb members and arbitrary unread rest — both pass. The concrete
run is at Σ_j at the predicted pass for j = 4..60 and 160, and the predicted word equals the concrete parallel word for
100,000 passes. Inside the cycle the only aged element read is moved, never opened, so nothing is forced.

## E98 — automatic parallel loop certificates (Theorem LP-par) on the census sample, 2026-10-26 (main agent)
code/par_loop_prover.py (values) and code/par_loop_prover2.py (lazy representation, DK_k·x = P^k(x)), run by
code/par_loop_census.py (one process per term, 240 s each). Results: data/par_loop_census.tsv, par_loop_census2.tsv,
par_loop_census2_calls.tsv (+ *_anchors.tsv re-runs with anchor offsets); union by code/par_census_union.py.
* **Loop and comb runs (85): 44 certified** — comb runs 21/22, loop runs 23/63. Values variant 44, lazy variant 43 (a
  subset of the 44, but each found in about a second instead of minutes).
* **Counter-type runs (65, call prover for the head runs): 5 certified** (lazy variant). These are linear call chains
  whose parallel runs are plain loops (cycle lengths 2n + 151, 2n + 4, 2n + 5).
* **In all, 49 of the 150 census-sample parallel runs are exact** (plus Theorem PL, which is among them).
* *Independent check* (code/par_cert_check.py): for every certificate, the concrete lazy parallel word over 400,000 passes
  is cut at the certified cycle starts. Every cycle word arises from the previous one by inserting at most m contiguous
  chunks (m = number of loops): values 44/44, lazy 43/43, counters 5/5. Two checker errors were found and fixed on the
  way, and neither was a soundness problem. (a) The checker assumed that the anchor M(n) coincides with the cycle start.
  When it lies a1·n + be1 passes later, cycle starts are αn + β − a1 apart; both provers now print the anchor offset.
  (b) The checker counted the cycle-finder block B, which need not be the block of the growing loop; it now tests chunk
  insertion.
* *Failures* (41 loop/comb, 60 counters): mostly 'token unfolded too often' (often surfacing as timeouts — a profile of
  S(S(SS)SS)S(SS) shows every candidate failing that way, so longer limits do not help), 'value too large' (values
  variant) and 'no comb pattern'. Cause, in S(S(S(SS))S)(SSS)(SS): the comb layers carry pending passes, nested
  through the comb. F = S(SS)K(P^4[]) with K = S(SS)(S(SS)) is a redex at every layer, so its evolution puts the next
  layer at a head, and forcing the top element unfolds the token about 60 levels deep. Layer-wise aging
  P^k(F^m(X)) = F_k^m(P^k X) holds for hnf-guarded contexts but not for these. The experimental variant
  code/par_loop_prover3.py (lookahead loop lemmas A(F^(ℓ+1)(O)) → A(F^ℓ(O)), ℓ ≤ 2, and loop variables treated as
  general atoms for non-normal families) proved none of the 41 uncertified loop/comb terms (data/par_loop_census3.tsv).
  Superseded by E100: with the settle check restricted (no token unfolding), the same extension proves 12 of the 41 and
  25 of the 60 uncertified counter-type runs.

## E99 — differential tests of the parallel machinery; unique-redex terms classified up to 15 leaves, 2026-10-26 (main agent)
*Parallel machinery* (code/lazy_par_fuzz.py): on random S-terms of 6–18 leaves, the lazy machine (Lemma LZ) gives the
same opcode word as direct ReplaceAll passes. Seed 1: 300/300 terms, 6,084 passes. Seed 2: 400/400 terms, 11,913
passes. Seed 3: 400/400 terms, 13,642 passes. The canonical aging rule used by the lazy-representation provers, once its pending passes are carried out by
direct passes, equals P^k(x) on 300/300, 400/400 and 400/400 random (term, k) cases (k ≤ 12, so past the 8-pass settle limit).
*Unique-redex terms.* code/ur_phi.py found that Φ-states Φ(c) = [c, S c, S c] recur in every unique-redex run at 13–14
leaves. code/ur_walk.py found that the Φ-elements obey Theorem UR's walk rule c′ = S q_m (S c) in 285 of the 289 runs at
13–15 leaves. The other 4 follow c′ = S c (S (S c)), the same walk ending at a different base. This led to Theorems UR-Φ
and UR-Φ-II (PROOF.md): one hand proof, symbolic base lemmas, and concrete transients (code/ur_phi_proof.py).
Enumeration (code/unique_redex.py, 3,000 steps): 0 terms with ≤ 9 leaves, then 2, 3, 10, 26, 68, 181 with 10–15 leaves.
**All 290 are proved to keep a unique redex for ever**: 286 by UR-Φ and 4 by UR-Φ-II. At 16 leaves there are 481 such terms (code/unique_redex.py now prints all of them), and
all 481 are proved (470 by UR-Φ, 11 by UR-Φ-II). At 17 leaves there are 1,316, and all are proved (1,290 by UR-Φ, 26 by
UR-Φ-II): **2,087 of 2,087 up to 17 leaves.** Transients are short: every one of the 2,087 runs reaches its certified
Φ-state within 2–21 steps (median 10). The unique-redex condition forces the Φ-regime almost at
once, which suggests an all-sizes proof via Lemma R's rounds (PROOF.md).
*Bases* (code/ur_bases.py 13): of the 19,074 normal forms with ≤ 13 leaves that are not of the form S p (S q), 89 are
bases, i.e. [β, S x, S y] reaches a Φ-state with a unique redex throughout. They give 13 return patterns: S x (S y)
(35; type A), S y (18; e.g. B itself, word 220), S (S y) (14), S y (S (S y)) (8; type II), S (S (S y)) (4), S S (S y) (3)
and seven single cases. The unique-redex runs up to 16 leaves settle on types A and II only; the other patterns occur at
most in transients. An all-sizes classification has to show, for every return pattern, that it either breaks
uniqueness in the following rounds (e.g. S^j y with j ≥ 2 does) or yields a covered machine.
*Round machine* (Lemma R′, code/ur_rounds.py): for every one of the 2,087 unique-redex terms up to 17 leaves, the round
machine’s prediction of the next round start [c′, S c′, d′] equals the concrete run in all 313,050 rounds checked (after fixing a recording bug that skipped 3-element lists)
(150 per term). In the steady state every round is a Φ-round. The B gadget explains why: its walk ends with two type-2
steps with t = S (through A = SSS), so its last push is S·v = S c′. Each is a linear counter, the same
in every evaluation order. 44 distinct bases are used (up to 17 leaves), all containing B = S(SSS)S. Each size's proofs run in under a
second.

## E100 — loops over evolving comb families: 86 of the 150 sample parallel runs certified, 2026-10-26 (main agent)
code/par_loop_prover3.py (PROOF.md, extension of Theorem LP-par). Loops over non-normal comb families are re-checked with
the loop variable as a general atom; lookahead ℓ ≤ 2; the settle check may not unfold comb tokens.
* The two terms that every earlier variant failed are certified: S(S(S(SS))S)(SSS)(SS) (cycle 5n + 20, anchor 5n + 16,
  cross-check 102/102) and S(S(SS)SS)S(SS) (4n + 23, 113/113). The earlier diagnosis, "nested pending passes force the
  whole comb", was wrong. The cascade came from the 8-pass settle check, not from the run (PROOF.md, correction).
* On the 41 uncertified loop/comb runs: 12 more certified. On the 60 uncertified counter-type runs: 25 more. On the 49
  earlier certificates: 48 re-certified (the exception, S(SSS)(SS)(S(SS))SSS, is certified only by the values variant).
* **Total: 86 of 150** — comb 21/22, loop 35/63, counter-type 30/65 (data/par_loop_census*.tsv). All 86 checked against
  400,000 concrete passes (code/par_cert_check.py: 12/12, 25/25, 48/48 for the new runs).
* The newly certified counters inspected (S(S(S(SSS)))S(SS)S, S(SS)S(SSS)(SSS)S, S(S(S(SS(SS))S))(SSS)S,
  S(SSS)(SSS)S(SSSS)) have linear call chains as head runs ('[call −1]' once per level) and linear loops (2n + c) as
  parallel runs. Same growth, no change of complexity class.
* Remaining 64: timeouts 40, token unfolding 17, no comb pattern 4, no growing-loop cycle 3.

## E101 — the Φ-regime of unique-redex runs, every size (Theorem UR-R), 2026-10-26 (main agent)
Data first (all 2,087 unique-redex runs ≤ 17 leaves, rounds counted from the first opcode-0 step). 1,896 runs have only
Φ-rounds, 189 have one non-Φ round, and 2 have two. This led to Theorem UR-R (PROOF.md), proved for every size
with Lemma R′. Every round ends (E1) with a type-2 step t = S, or (E2) with a type-1 step while v = S (needs d = S). An
(E1) round whose u before the last step is S z kills the run within two rounds. So Φ-rounds are followed by Φ-rounds,
at most three non-Φ rounds occur, every Φ-element's left spine ends with B = S(SSS)S, A = SSS, S, and
c′ = S c or S z (S^(m−1)(S c)). In the Φ-regime the run is a deterministic map on the Φ-element alone.
code/ur_regime_check.py checks (a)–(d) on all 2,087 runs, and all hold: (a) non-Φ prefix ≤ 3; (b) B, A, S ending;
(c) the c′ formula; (d) type-1 steps before the last preceded by t = S. m-values met: 0 (1,757 rounds), 1 (120,814),
2 (2,456).
Two checker bugs were found on the way, and neither affected any theorem. Rounds were not recorded when the list had exactly
3 elements (t₀-like terms, also in code/ur_rounds.py; rerun: 2,250/2,250 and 72,150/72,150 rounds). And the hash-consed
ids of A and B went stale after a node-table reset, which made 40% of the B, A, S tests fail spuriously.
Open, the last step to a classification at every size: Ψ's orbits. Hand analysis so far: the pointer z of Ψ(c) is c
itself (type II, which persists), the inner part of the new top layer (when z's walk starts with a type-1 step), or
inherited from the element it points to. Inherited pointers move strictly back in time, so the chain ends, as in
Theorem UR-Φ's corollary. Cases m ≥ 3 and non-consecutive m = 2 remain to be ruled out or classified.

## E102 — orbits of the Φ-map: only types A and II, 2026-10-26 (main agent)
code/ur_psi_explore.py samples Φ-elements directly, as random normal forms whose left spine ends with B, A, built from
random type-1 layers S x and type-2 layers S x t (t = S or S y), and iterates the exact round map Ψ. Seed 1 (20,000 samples, 40
rounds): 12,674 die, 6,959 type A, 367 type II, 0 other. Seeds 2–4 (20,000 each, 80 rounds): 12,644 / 6,975 / 381,
12,662 / 6,992 / 346, 12,654 / 6,995 / 351 — again 0 other. Supports Theorem UR-C (PROOF.md: proof sketch, every size).

## E103 — the pointer-transition rules of Theorem UR-C, machine-checked, 2026-10-26 (main agent)
code/ur_pointer_check.py computes, for every round of a Φ-orbit, the walk, m, and the pointer (pred / pos0 / cons) and
checks the predicted transitions T0 (m = 0 → single type-1 layer at position 0, pointer = the new element), T1 (walk of
the pointer starts with a type-1 layer → m = 1 before and after, pointer = previous element), T2 (walk of the pointer
starts with a type-2 layer → m inherited, pointer inherited and a proper subterm of the old pointer, or self), plus
c_{k+1} = S c_k / S z_k X_k and the eventual regime.
* Real runs (all 2,087 unique-redex terms ≤ 17 leaves, 60 Φ-rounds each): T0 1,757/1,757, T1 61,669/61,669,
  T2 61,794/61,794; eventual regime type A with a fixed base 2,046, type II 41, other 0.
* Sampled Φ-orbits (4 seeds × 20,000 random Φ-elements, 60 rounds; 29,366 orbits that keep a unique redex):
  T0 18,148, T1 847,253, T2 896,559 transitions — all as predicted; type A 27,921, type II 1,445, other 0.
These are exactly the lemmas of the proof of Theorem UR-C (PROOF.md), which is now a complete hand proof: every
unique-redex S-term is eventually a linear counter of type A or II, at every size and in every evaluation order.

## E104 — correction: unique-redex counts (data-file errors, no theorem affected), 2026-10-26 (main agent)
While enumerating thin runs (second element of spine ≤ 1, elements not necessarily normal: code/thin_runs.py), the counts
at 13 leaves disagreed. Cause: data/unique_redex_13.txt from an earlier session was **cumulative** (it listed all terms of
10–13 leaves) and **truncated** (an older code/unique_redex.py printed at most 40 terms). Its header says 26 unique-redex
terms at 13 leaves, but only 25 of them were listed. So (1) the 15 terms of 10–12 leaves were counted twice in every
total, and (2) one 13-leaf term, S(S(SSS))(S(SSS))SSSS, had never been checked. The file is regenerated
(26 terms at 13 leaves; the old one is kept as data/unique_redex_3_13_truncated_old.txt). code/unique_redex.py now prints
every term it finds.
Corrected numbers, all checks rerun on the clean files (data/ur_aggregate_clean.txt): 2, 3, 10, **26**, 68, 181, 481,
1,316 terms at 10–17 leaves, **2,087 in all** (not 2,101): 2,046 by UR-Φ and 41 by UR-Φ-II. All proved, including the
previously unchecked term. Round machine 313,050/313,050 rounds. UR-R: (a)–(d) on all 2,087; non-Φ rounds per run 0
(1,896), 1 (189), 2 (2). Transients 2–21 steps (median 10). 44 distinct bases, all containing B. UR-C's real-run
transitions: T0 1,757, T1 61,669, T2 61,794, all as predicted; type A 2,046, type II 41. The theorems themselves (UR-Φ,
UR-Φ-II, UR-R, UR-C) are unaffected, being hand proofs whose checks pass on the corrected data. PROOF.md, STATUS.md,
NEXT_STEPS.md, PRIZE_ASSESSMENT.md and the session summary are corrected.

## E105 — thin runs: the class just beyond unique-redex, 2026-10-26 (main agent)
*Thin* head runs keep the second list element of spine ≤ 1 at every step but may have list elements with redexes, so
opened elements can have spine ≥ 3 (code/thin_runs.py). Enumeration (3,000 steps): thin runs are exactly the
unique-redex ones up to 12 leaves. At 13 leaves there are 30 (26 unique-redex + 4 not), at 14 leaves 88 (68 + 20), at
15 leaves 275 (181 + 94). The 118 thin runs that are not unique-redex (data/thin_nonur_13_15.txt) have opcodes up to 5.
All 118 stay thin for 20,000 steps, and **the loop prover certifies all 118 as exact loop runs** (per term).
96 settle into Φ-rounds like the unique-redex runs. 22 alternate Φ-rounds with *B-rounds* [B, S B, d], d ≠ S B. B's walk
(type 2 with t = S, type 2 with t = S, end) sends any (u, v) to c′ = v with the last push S·v, so a B-round is always
followed by Φ(d): the gadget B is a Φ-maker in these runs too. Theorems UR-R/UR-C do not cover thin runs, because
type-k steps with k ≥ 3 reset the registers to (a_2, a_3) and can end a round with c′ = a_3, d′ = a_4.
NEXT: extend Lemma R′ and Theorems UR-R/UR-C to type-k steps; all data say thin runs are linear counters too. Note
that thin runs are a head-run class, not order-independent (their elements contain other redexes).
*Round anatomy* (code/thin_rounds.py, all 408 thin runs ≤ 15 leaves, second half of 6,000 steps). Rounds are labelled
(start, m, widest spine, ending). Only 7 steady-state sets of round kinds occur:
382 runs (Φ, 1, 2, E1) [type A]; 4 runs (Φ, 2, 2, E1) [type II]; 9 runs B-rounds + (Φ, 1, 3, E3); 9 runs B-rounds +
(Φ, 2, 3, E2); 2 runs (Φ, 0, 3, E3) + (Φ, 1, 2, E1) + (other, 1, 2, E1); 1 run (Φ, 1, 3, E3) + (other, 0, 2, E1); 1 run
(Φ, 2, 3, E2) + (other, 0, 2, E1). The new endings E3 (a spine-3 step S S S B whose a_2 = S ends the walk, giving
c′ = a_3 = B and d′ = the old v) and E2 (a type-1 step at v = S) send the run through one B-round, which hands back Φ(d).
Thin runs are thus the unique-redex patterns with an optional B-round inserted. A class theorem is within reach of the
UR-R/UR-C method, but adds little: all 118 are already certified per term, and the class is small and order-dependent.

## E106 — adversarial search for irregular head runs: the most complex runs found are certified loops, 2026-10-26 (main agent)
code/irregular_hunt.py: an evolutionary search over S-terms of 15–60 leaves, scoring each head run by the Lempel–Ziv (LZ76)
complexity of its opcode word over 20,000 steps, normalised by N / log2 N. Calibration: random 4-letter word 1.97,
constant word 0.001, the unique-redex counter t₀ 0.139, simple loops 0.054. Seven independent searches (populations
40–60, 6–15 generations, ≈ 1,300 evaluated terms) reach at most 0.41: far below random, and still structured (long
2-blocks separated by short varying segments). The 30 highest-scoring distinct runs (data/irregular_top.txt) were given
to all head-run provers (code/prove_any.py): **30/30 PROVED, all by the loop prover** (exact growing-loop cycles, up to
10 loops per cycle, non-linear comb families). Even a search that deliberately pushes towards irregularity finds only
regular, certifiable runs. This is evidence for R″_PUP, not a proof; the search space is tiny compared with all terms.

## E107 — Lean 4 formalisation of Theorem UR-R's core, 2026-10-26 (main agent)
lean/URCore.lean, checked with an installed Lean 4.35.0 toolchain, called directly. Nothing was downloaded and the elan
default was not changed. code/lean_check.py compiles it and lists the axioms of every theorem: 11 theorems, 0 errors,
axioms {propext, Quot.sound} only, no sorry. Formalised: the head machine on lists, normal forms, the unique-redex
condition, the end lemma, the dying lemma, the Φ-successor lemma, the walk lemmas, Lemma R (round starts are reached),
entry into the Φ-regime (`reach_phi`) and Φ-states for ever (`phi_forever`). Two of my own slips were caught by Lean on
the way: a wrong step count (3, not 4) in an explicit E2 continuation, and an elaboration-order issue, a goal with an
undetermined metavariable. Neither was in the mathematics of the hand proof.

## E108 — Theorem UR-C in Lean; descending one-redex evolutions (a correction); Theorem DK, 2026-10-26 (main agent)
*Lean.* lean/URCore.lean now formalises Theorem UR-C. The Φ-map is the final v register of the round machine (`fv`,
`psi`). Walk shapes `noOne`, `PredA`, `PredII`; `walk_out`, the outcome of every valid walk in five cases (no type-1
layer; a single one at position 0; "pred" with a strictly smaller pointer; "cons"; last type-1 after (2, S));
`rv_wide` (no type-1 layer after v has two arguments); the death lemmas; type A and type II persistence (`periodA`,
`periodII`); and the pointer induction `st_ind` (strong induction on the pointer's size). Main results:
`ur_classification` and `ur_counter`. code/lean_check.py: exit 0, 0 errors, 19 theorems listed, no sorry; axioms
propext, Classical.choice (from `by_cases`) and Quot.sound. Lean caught four of my slips in the first draft, all the
same kind: `simp only` had already turned an equation into True, so `rfl` no longer fitted. None was in the mathematics.
*Descents (correction).* The term-level condition "exactly one redex at every step" is wider than the list-level one.
From the active list [S, S p q, c] (all normal) the head step gives S c (S p q c), and the only redex is the argument.
code/unique_redex.py stopped there. code/descent_runs.py follows the term-level evolution with descents (2,000 steps).
Nothing survives up to 8 leaves. At 9 leaves three terms survive: S(SS)S(S(SSS)S) and S(S(SS))(S(SSS))S (one descent
each, then head-unique) and S(S(SS))(S(SS))(SS) (1,936 descents). At 13 leaves, 166 terms survive:
* 26 head-unique from the start;
* 33 that descend only before the first head step;
* 75 with 1–3 descents after it, then head-unique;
* 32 that descend at about 97% of steps.

Independent check (plain Python trees, no hash-consing, count every redex, contract the unique one): exactly one redex
at each of 400 steps for all three 9-leaf terms. For S(S(SS))(S(SS))(SS) the contracted redex's depth reaches 371. For
SS(SS(S(S(SS))(S(SS))))(SS) it is 275 after 300 steps.
*Theorem DK.* code/descent_classify.py: every forever-descending term (≥ N/2 descents in N = 2,000 steps) at 9–14 leaves
(1, 2, 5, 13, 32, 87) has the K-family steady state [S, Y_j, Y_n] (j < n), [SS, SS, Y_n] from step 500 on, where
Y_0 = K = S(SS)(SS) and Y_{n+1} = S S Y_n. code/descent_k_proof.py checks rules D1–D3 on terms with opaque atoms. It then
follows each of the 140 terms concretely, with exactly one redex checked at every step, until the active list is
[SS, SS, Y_n]: 140/140 enter by step 5. So all are PROVED: descending linear counters with opcode word u ∏ 1 0^{n+1}.
*Triple probes (E108, continued).* code/descent_triples.py enumerates 3-element restart lists [p, q, c] of normal forms
directly (the term S p q c), since every descent restarts the evolution from such a list. All 704,969 triples with
p, q, c ≤ 7 leaves (89 normal forms): 8 forever-descending. All 186,864 triples with p ≤ 10, q ≤ 5, c ≤ 4 leaves: 1.
All have the K-cycle steady state. Recorded as Conjecture DK* (PROOF.md): every forever-descending one-redex
evolution enters the K-cycle. The low-point structure of segments is noted there as the starting point for a proof.
*Novelty check (E108, continued).* BEKW §2 already contains the descending mechanism: K·K = S(SS)(SS)(S(SS)(SS)) is the
Zachos term STT(STT), T = SS, recorded here before as E20, with novelty withdrawn there for Theorem C. BEKW cite J.
Waldmann, "Nimm Zwei" (TR IR-432, VU Amsterdam 1997) for a characterization of all terms whose reduction graph is an
infinite line, i.e. all one-redex-forever terms. Not read. Theorems UR-R/UR-C/DK very likely overlap with it, so no
novelty is claimed.

## E109 — size-change closure on leftmost walks in the resisting component (empirical), 2026-10-27 (main agent)
Target: the leftmost-path finite half (PROOF.md, Theorem LP1 "remaining obligation"; FAILED_APPROACHES 22).
code/lw_anatomy.py: every term ≤ 11 leaves in joint L36 × M35 classes {(14,28), (14,26)}. Counts 3,377 at ≤ 10 leaves
and 8,569 at 11 leaves. The walks take at most 7 size-increasing (computed) steps; at 11 leaves 6,964 end at S and 1,605
in ⊥. The longest walks run through the shapes SSSS X Y → SS(SS) Y → Y.
code/lw_sct.py (subterm arcs; states = joint class of the node plus classes of its arguments; observed transitions only):
the Lee–Jones–Ben-Amram closure has 6 idempotent self-loops with EMPTY graphs. Threads cannot pass through the new
composites q·v created by computed steps: the obstacle of FAILED_APPROACHES 22.
code/lw_sct_size.py (size arcs between ALL slots, slot −1 = the whole node; sound for size-change termination, because
each arc is a true size relation of its concrete step and size is well-founded):
* ≤ 9 leaves: 219 abstract edges, closure 630, 0 bad loops;
* ≤ 10 leaves: 840 edges, closure 6,246, 0 bad loops;
* ≤ 11 leaves: 2,506 edges, closure 39,455, 0 bad loops.

At ≤ 10 leaves only 7 idempotent self-loops exist, and in all 7 the WHOLE NODE strictly shrinks.
Reading: EXPERIMENTALLY SUPPORTED, not a proof. On observed walks, revisiting a fine state (node class plus all argument
classes) always happens at a smaller node. A proof still needs (i) a FINITE abstraction (the fine state space grows:
204 → 629 → 1,485 states) and (ii) completeness of its transitions for all sizes, i.e. a symbolic summary of the
computed step (the tail chain of Theorem Q10 ends at S v_k (q_k v_k); leftmost child v_k = q_{k−1} v_{k−1} or e_m).
Size arcs remove the composite obstacle; state completeness remains.

## E110 — construction agent (started at the user's request): obstructions, no construction, 2026-10-26/27
Full log: agent_work/LOG.md. Final report: no universality construction, no 2-counter simulation, no looping transfer,
and no provably non-R″_PUP run. Machine-checked: Theorem OT and Lemma RC (lean/AgentOT.lean), Lemma OC, OC1 and
no_transparent (lean/AgentOC.lean). Both recompiled by the main agent with standard axioms only and no sorry; the
definitions of step, ppy, ordered and badPairL were read and match the statements. Both are now in verify_all. The
bounded searches are listed in PROOF.md ("Construction-agent obstruction theorems"). Process note from the agent: two
searches grew to 4.5 and 7.6 GB, were killed by PID (68356, 119696) and rerun with memory truncation; no agent
processes remain.

## E111 — construction agent phase 3: dirty wrappers, duplication, the re-execution regime, 2026-10-27
Machine-checked (re-verified by the main agent):
* Theorem OTD and Lemma FH (lean/AgentOTD.lean; FH uses axiom propext only);
* Theorem SL (lean/AgentSL.lean, 790 lines);
* canonical_innermost (lean/AgentCANON.lean, 1,288 lines).

All four are in verify_all. Multi-level phase-3 claims are computationally certified only: exhaustive for right combs
≤ 11 leaves and ordered contexts ≤ 10 leaves, plus 70,000 random data. A negative control shows that shapes alone do
not suffice. Details, scope and definitions: PROOF.md, "Construction-agent obstruction theorems"; agent_work/LOG.md.

## E112 — pushdown abstraction of leftmost walks (no sizes), 2026-10-27 (main agent)
code/lw_pushdown.py abstracts a leftmost walk as a stack of chain-value classes (from Theorem Q10's tail-chain
equations, the child of a computed step is q_{k−1}·(…(q_0·e))) over an opaque base, with class-level tail chains.
Flag-0 start classes: 66 of 69. SCCs containing a non-structural step:
* stack height ≤ 1: 584;
* ≤ 2: 1,551;
* ≤ 3: 2,360.

Almost all are self-loops [(b, β)] → [(b, β)], i.e. countdown steps such as N_i N_k ↦ N_{i−1} N_k that keep their
class while the top symbol shrinks. So the class abstraction cannot be made sound and precise without size
information. This confirms FAILED_APPROACHES 22 from another angle.

## E113 — size-change closure over FINITE abstractions of leftmost walks: none survives, 2026-10-27 (main agent)
code/lw_sct_coarse.py (worklist closure; size arcs over fixed parameters: the node, its first three and last two
arguments; SCT_MODE selects the state). Idempotent self-loops with no strict self-arc ("bad"):

| state abstraction | data | states | closure | bad |
|---|---|---|---|---|
| node class only | ≤ 9 leaves | 2 | 7,588 | 315 |
| class + number of args | ≤ 9 | — | — | 28 |
| class + first/last arg classes | ≤ 9 | — | — | 10 |
| class + nargs + first/last | ≤ 9 | — | — | 6 |
| class + nargs + classes of first 2 and last 2 args | ≤ 9 / ≤ 10 | 198 / 601 | 750 / 5,809 | 0 / 0 |
| same, width 3 | ≤ 9 / ≤ 10 | 204 / 627 | 630 / 6,259 | 0 / 0 |
| width 2 | ≤ 11 leaves | 1,402 | 47,423 | **4** |
| width 2 | ≤ 10 + 3,000 random 12–22 leaves | 1,565 | 300,323 | **68** |

Reading: a fixed finite window passes on small terms and fails as larger terms add transitions. Only the unbounded
fine state of E109 passed. So size-change termination over finite class abstractions does not prove the
leftmost-path half; a proof needs an infinite-state but structured abstraction (stack plus sizes) or a new idea.
(Recorded as FAILED_APPROACHES 29.)

## E114 — leftmost-path finite half: generalised Lemma P with opaque bottoms; class graphs; tail chains, 2026-10-27 (main agent)
*Generalised Lemma P (PROVED, hand; same proof as Lemma P):* for a closed list L and ANY two terms D1, D2 (closed, or
containing atoms), if the head run of L ++ [D1, D2] stops — at a list of length ≤ 2 or at an atom-headed front — then the
leftmost Böhm-tree path of S·L is finite. (At a one-child node [x] the bottoms become [D2, D1·D2]; at a two-child node
[x, y] they become [D1, y·D1, D2] and the prefix argument of Lemma P applies.) For the resisting component
{(14,28), (14,26)} closed bottoms never work (M35 class 28 is dead under every argument, class 26 under every two), so
the test uses atoms a, b. code/lw_atoms.py (data/lw_atoms_9.txt): at 7 leaves all 33 component terms stop at an
atom-headed front; at 8 leaves 166 of 171 stop, but 5 grow past 200,000 leaves (e.g. SSS(SS)S(SS), 2,013 steps) although
their leftmost paths are finite. The reason: at a one-child node the bottom element D1·D2 or y·D1 becomes the top, so the
run continues into S-headed code after the path has ended. So the criterion is sufficient but not necessary, and it
does not prove the half (FAILED_APPROACHES 30).
*Class graphs (code/rw_classgraph.py).* Over the joint magma (path model × M35), restricted to path-flag-0 classes in F,
with an edge to every possible child class: leftmost (L36, 69 joint classes) has 2 nontrivial SCCs, {(14,16)} and the
known {(14,26), (14,28)}; rightmost (R19, 78 joint classes) has 11, one of them with 20 classes. Class-level edges cannot
tell computed steps from structural ones, so the rightmost half is harder than the leftmost at this level.
*Tail chains (code/lw_chain.py 10).* Computed steps that stay in the component write the child as a right comb
q_{k−1}·(…(q_0·e_m)) over the node's last argument with k = 0…6 and 201 distinct chains at ≤ 10 leaves (e.g. q = [S(SS)],
[SSS(SS)], [SSSS(SS), SSSS(S(SS(SS)S)S)]). No small family of chain shapes covers the component.
*C6 completeness half at class level (code/c6_classgraph.py, c6_shrink.py).* Over the 113-element joint magma P39 × M35
the 17 nodes (⊥_P, F_M) form ONE strongly connected component under "has a ⊥_P child class", so no class-level acyclicity
argument exists. Sizes do not help either: at ≤ 10 leaves, of 497 computed ⊥_P nodes only 126 have a smaller ⊥_P hnf
component (e.g. SSS(SS)SS → S(S(SS)S)S(S(SS)(S(S(SS)S)S)), 7 → 13 leaves). Conjecture C7 (a ⊥ at depth ≤ |t| − 3) therefore
needs a measure other than node size.
