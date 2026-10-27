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
