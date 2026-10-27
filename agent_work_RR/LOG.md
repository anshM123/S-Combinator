# agent_work_RR LOG (race-material / universality agent, 2026-10-27)

## 2026-10-27 11:32 EDT start
Task: construct the race material required by Theorem RR (agent_work_P/LOG.md, 11:15 entry and FINAL item 11), or
find precise obstacles. Deadline 15:00 EDT. Write only inside agent_work_RR/. Memory cap 2M hash-consed nodes per
search, timeout <= 30 min per search.

## 2026-10-27 11:34 EDT reading done; exact hypotheses of Theorem RR (as stated in agent_work_P/LOG.md 11:15)
* ONE term t_(P,Q) per pair of polynomials (computable map (P,Q) -> t_(P,Q)); its single ReplaceAll run must create,
  for EVERY y in N^r, a race node: a subterm occurrence S A_y B_y that evolves as S P^j(A_y) P^j(B_y) (argument of an
  hnf, or a waiting element), with h_par(A_y) = c + P(y), h_par(B_y) = c + Q(y); a fixed bounded-time pattern pi
  matches such a node exactly when the left side is head-normal and the right side is not, and (b) matches nothing
  else in the run. Then 'some subterm matches pi' is r.e.-complete (MRDP). r >= 2 is needed (r = 1: exists y with
  P(y) < Q(y) is decidable).
* So a per-y family {t_y} of separate closed terms is NOT enough: the encoder must produce ONE term whose run
  generates race nodes for all y (data-dependent construction by a data-blind skeleton). A per-y family is the
  'race-node level' ingredient; the generator is the open part.
* Conventions (PROOF.md Lemma 2, code/lazy_par.py): a list [e1, e2, ...] is the term S e1 e2 ...; head step
  [a, b, c] ++ R -> ch(a) ++ [c, b.c] ++ R; ReplaceAll pass: P(S a1 a2 a3 a4..am) = a1 a3 (a2 a3) P(a4)..P(am) (m >= 3),
  P(S a1 .. am) = S P(a1) .. P(am) (m <= 2). h_par(t) = first n with P^n(t) head-normal (spine length <= 2).
* Tools: Theorem N (numerals iterate calls, head time 2n + (n-1)T(P)), Theorem CA (tree calls, T(seq) = sum T + k),
  Theorem CA-par (tree calls with normal-form arguments keep their head times under ReplaceAll).

## 2026-10-27 11:49 EDT E1: one-numeral templates have no polynomial hnf times; why (C2) -- COMPUTATIONALLY CERTIFIED (scan) + PROVED-conditional (C2)
* shape_scan.py 5 0 7 3 2000: every template with <= 5 leaves over {N = n-bar, S} (N at least once) whose ReplaceAll
  hnf time exists for n = 1..7 (cap 2000 passes) has an EVENTUALLY CONSTANT hnf time (boundary effects only, e.g.
  N(NSS)S: 1, 6, 6, 6, ...); the others have no hnf within the cap for some n <= 7. 0 linear, 0 polynomial.
* Reason (PROVED from Conjecture C2 + Corollary PT-F): C2 (PROOF.md, 'fast-or-never', certified for |t| <= 19) says a
  term with an hnf reaches it within 2|t| head steps, and h_par <= h_lo (Cor. PT-F, MACHINE-CHECKED). So
  h_par(A) <= 2|A|: a race process with hnf time c + P(y) has SIZE >= (c + P(y))/2. Numeral-encoded parameters
  (size O(y)) can only give hnf durations O(sum y_i); a non-separable hnf duration y1*y2 needs a process of size
  Omega(y1*y2), i.e. the generator must itself build a structure of size ~ y1*y2 (a unary product) -- the hard
  construction problem in another form. Nested numeral iteration (Theorem N, time n*T(P)) is a CALL: it never reaches
  an hnf (consistent with C2).
* Consequence for the design: use an event whose time is NOT bounded by the size, i.e. a Boehm-tree-level event.
  Variant Theorem RR' (normal forms instead of hnfs) -- PROVED by the same argument: normal forms are fixed by every
  pass, so if the race node evolves as S P^j(A) P^j(B), a pattern 'left side normal, right side not normal' (+ a marker)
  fires iff n_par(A) < n_par(B) (n_par = first pass at which the term is normal). The detector is then a finite tree
  automaton (linear time), the class Theorem RR concludes with anyway; but it is no longer a bounded-time pattern.

## 2026-10-27 12:09 EDT E2 + Theorem B2: a BILINEAR ReplaceAll normalisation time from two numerals, write-free -- PROVED + COMPUTATIONALLY CERTIFIED
* Scan (nf_scan.py; n_par = first k with P^k(t) a normal form, direct passes code/parallel_eval.step_fn):
  one numeral, <= 4 leaves over {N, S, s=SS}, n = 1..8: e.g. n_par(N N S) = n^2 + 2n - 2, n_par(N s N) = n^2 + n - 1
  (nf4.txt). Two numerals, 3 leaves over {N, M, S, s}, n, m = 1..6 (nf3_two.txt): exactly 4 non-separable templates:
  N M S: nm + 2n - 2;  N s M: nm + 2n - m - 1;  and the mirror images M N S, M s N. All four are WRITE-FREE (no closed
  term applied to a data-containing argument): 'data holding data' (n-bar absorbs m-bar), allowed by Lemma 9 / Thm J.
* Pass identities used (Lemma LZ; numerals k-bar = S S (k-1)-bar, 1-bar = SS; U_m(R) := m-bar S R, V_m(R) := S S (m-bar S) R):
  P(U_{m+1}(R)) = V_m(P(R));  P(V_m(R)) = S R U_m(R);  P(U_1(R)) = S R (S R);  P(S A B) = S P(A) P(B).
* Lemma U -- PROVED. For m >= 1 and every term R with n_par(R) = r finite: n_par(m-bar S R) = max(2m - 1, m + r).
  Proof: induction on m. m = 1: P(U_1(R)) = S R (S R), normal iff R is: 1 + r = max(1, 1 + r). m >= 2: P^2(U_m(R)) =
  S R1 U_{m-1}(R1) with R1 = P(R), n_par(R1) = r' = max(r - 1, 0); an hnf S A B is normal iff A and B are, and evolves
  as S P^j(A) P^j(B); so n_par = 2 + max(r', max(2m - 3, m - 1 + r')) = max(2m - 1, m + r) (cases r >= 1, r = 0). QED
  Reading: each spine level holds the copy of R back by one pass (R is the third argument of the redex V_k(R), which a
  pass does not enter), so m-bar S R ADDS m to the normalisation time of a slow R: a sum gadget.
* Theorem B2 -- PROVED. For all n, m >= 1: n_par(n-bar m-bar S) = n*m + 2n - 2.
  Proof: P(n-bar m-bar S) = S m-bar ((n-1)-bar m-bar) S and P^2(n-bar m-bar S) = U_m((n-1)-bar m-bar S) (n >= 2; Lemma LZ (i)
  twice; the redex arguments are not entered). By Lemma U, T(n) = 2 + max(2m - 1, m + T(n-1)) = 2 + m + T(n-1) because
  T(n-1) >= m. Base: 1-bar m-bar S = S S m-bar S -> S S (m-bar S); m-bar S -> S S ((m-1)-bar S) -> ... -> S S (1-bar S)...
  and 1-bar S = SSS is normal, so T(1) = 1 + (m - 1) = m. Hence T(n) = m + (n - 1)(m + 2) = nm + 2n - 2. QED
* Certified: bilinear_check.py 30 30 -> 900 of 900 (n, m) <= 30 agree (max 432,107 hash-consed nodes, 21.7 s).
* Contrast: by C2 + Cor. PT-F the HNF time of any term is <= 2|t|; the NORMALISATION time n_par(n-bar m-bar S) ~ nm is
  quadratic in the size 4n + 4m + 1. The product is produced by the critical path through nested copies (a delay chain),
  not by a long head run.

## 2026-10-27 12:22 EDT Lemma U and Theorem B2 -- MACHINE-CHECKED (lean/Bilinear.lean)
* agent_work_RR/lean/Bilinear.lean (standalone, Lean 4 core; T, pass, passN verbatim from agent_work_P/lean/ParTime.lean,
  whose pass is cross-checked against the Python ReplaceAll pass by 30 kernel-checked instances; isNf = 'no redex').
  `cd code && python lean_check.py ../agent_work_RR/lean/Bilinear.lean` -> "exit 0, 0 errors, 3 theorems checked ...
  LEAN OK: no errors, no sorry"; axioms propext, Classical.choice, Quot.sound.
  - `lemmaU`: (forall i, isNf (passN i R) <-> r <= i) -> isNf (passN i ((k+1)-bar S R)) <-> 2k+1 <= i /\ k+1+r <= i.
  - `num_S_time`: (k+1)-bar S is normal from pass k on, exactly.
  - `theoremB2`: isNf (passN i ((j+1)-bar (k+1)-bar S)) <-> (j+1)(k+1) + 2j <= i, i.e. n_par(n-bar m-bar S) = nm + 2n - 2.
  - two `decide` instances: 4-bar 4-bar S (numP 3) is normal at pass 22 = 4*4 + 2*4 - 2 and not at pass 21.

## 2026-10-27 12:40 EDT E3-E5: no higher-degree or sum-of-products clocks among small templates -- COMPUTATIONALLY CERTIFIED (finite scans)
* delay_scan.py 3 5 40 3000: no template X <= 3 leaves over {N, M, S, s} (N, M both present) with X S R holding a slow
  R (= 40-bar S) back by a non-separable polynomial Delta(n, m) (n, m <= 5). (4-leaf scan delay_scan.py 4 4 30 2000
  running in the background -> delay4.txt.)
* tri_check.py / tri_scan.py 4 4 2000 (all 4-leaf templates over {N, M, K, S, s} with all three numerals, grid {1..4}^3):
  no degree-3 term; the polynomial ones are degree 2 (e.g. N(M K S) = n + mk + 2m - 3, Lemma U applied to B2);
  the non-polynomial ones are max-plus (e.g. N S (M K) = max(2n - 1, n + m - 1), Lemma U with n_par(m-bar k-bar) = m - 1).
  N M K S, N (M K) S, N (M K S) S etc. do not normalise within the caps: an iterator applied to a non-numeral spine
  generator grows exponentially (probe3.py: 2-bar (2-bar 1-bar S) S, size x1.4 per pass for 40 passes).
* word_scan.py 5 6 3000 (single datum D = (SS.)^a (Z b-bar), Z closed <= 5 leaves; processes D D S, D S): the only
  non-separable exact clock is Z = SS, where D is the numeral (a+b+1)-bar and D D S = s^2 + 2s - 2 with s = a + b + 1,
  a function of ONE linear form (useless: one parameter). Other separators: no normal form within caps or max-plus.
* thmC_probe.py: the data W_r = (SS.)^r K of Theorem C's Boehm-tree counter are not benign clocks: W S normalises at
  r + 7, but W S S, W W S, 3-bar W S, W 3-bar S do not normalise within caps (the base K restarts the counter).
* swap_search2.py 8: no closed Z <= 8 leaves with Z u X Y ->* [X, u, ...]; X reaches the front only with u X as its
  argument (u X, u X (X (u X)), ...), as Lemma 10 requires (an X-headed term containing u contains X twice).

## 2026-10-27 12:42 EDT E6-E7: two-letter words and natural junk -- COMPUTATIONALLY CERTIFIED (finite scans), negative
* delay_scan.py 4 4 30 2000 (959 s): no 4-leaf delay gadget X over {N, M, S, s} with a non-separable delay either.
* layer_scan.py 5 5 3000: data built by FRONT-WRAPPING with two letters, D = L^b (a-bar) and D = (SS.)^a (L^b SS),
  L closed <= 5 leaves, processes D D S, D S, D S S, a, b <= 5: NO exact polynomial clock whose quadratic part is a
  non-degenerate form (c11 != 0 and c11^2 != 4 c20 c02). So in every case found the clock depends on the word only
  through ONE linear form of the letter counts (one effective parameter).
* junk_nf.py (exact lazy ReplaceAll machine, 400-600 passes): race-shaped products S A B pushed as waiting elements in
  the runs of the binary counter SSS(SS)S(SS(SS)) (90), K0 S(SS)S(S(S(SSS)))S (125 in 295 passes), the E36 reload term
  (2), Theorem PL's loop (11) and the two square runs of Theorem NL (86, 118): in NONE are both sides non-normal
  processes that normalise (n_par cap 200). Natural junk is not race material for normal forms either; race material
  has to be engineered (agrees with agent_work_P's hnf probe).

## 2026-10-27 12:55 EDT Race-node family with a marker pattern -- PROVED (durations: Theorem B2) + COMPUTATIONALLY CERTIFIED (pattern)
* Encoder (per parameter triple; a FAMILY, not a single generating term): t(n, m, k) := S (S Mk A) B with
  A = n-bar m-bar S, B = k-bar k-bar S, Mk = N_12 = S(S(...(S S))) (the nest with 13 leaves, a normal form).
* Durations (Theorem B2, MACHINE-CHECKED): n_par(A) = nm + 2n - 2, n_par(B) = k^2 + 2k - 2. The root is an hnf, so it
  evolves as S (S Mk P^j(A)) P^j(B) (P(S x y) = S P(x) P(y); Mk is normal).
* Pattern pi: an occurrence of S (S Mk X) Y with X normal and Y not normal (a finite-tree-automaton check; linear time).
  It fires at the root exactly at the passes j in [nm + 2n - 2, k^2 + 2k - 2), hence ever iff nm + 2n < k^2 + 2k:
  a NON-SEPARABLE comparison.
* 'pi matches nothing else' -- COMPUTATIONALLY CERTIFIED: race_family.py 11 scans every distinct subterm at every pass
  until both sides are normal: 1331 of 1331 triples (n, m, k) <= 11 agree (pi fires at the root exactly on the
  predicted passes, never elsewhere; it fires in 702 cases). Reason (proof sketch, not formalised): every term in the
  runs of A and B has the shapes of Lemma U / Theorem B2 (numerals S S x, S R U, S S (k S) R, ...), in which S is never
  applied to a single argument that is itself S-headed with one argument except S S; so no nest of depth >= 2, let alone
  N_12, occurs except the marker.
* What this is: race-node-level material meeting Theorem RR' for the FAMILY (one closed term per parameter tuple), with
  exact non-separable durations. What it is NOT: Theorem RR's hypothesis, which needs ONE term whose single run
  creates such nodes for all tuples (the generator), and prescribed polynomials P, Q (only B2-type durations here).

## 2026-10-27 13:00 EDT E8: per-letter weights of front-wrapping layers are tied -- COMPUTATIONALLY CERTIFIED (finite scan) + heuristic reason
* weight_scan.py 6 4 3 2500: for D = L^b(a-bar) with L closed <= 6 leaves (65 layers), the spine-role delay
  (n_par(D S R) - n_par(R), R = 40-bar S) and the iterator-role count (from n_par(D k-bar S), k = 3, 5) are both exact
  affine functions of (a, b) ONLY for L = SS (the numeral layer itself: weights (1,1) and (1,1), proportional). For
  every other layer one of the roles is non-affine or does not normalise within the caps.
* Heuristic reason: the spine role of a datum is its iterator role instantiated at X = S (D S R vs D X S), so a layer
  that acts uniformly ('X Y -> X Y (rest X Y)', c times) has weight c in both roles; a non-proportional layer would
  have to act differently according to the SHAPE of its argument X (data-driven inspection of a datum).
