# PROOF — exact statements and arguments

Conventions. S-terms: `T ::= S | (T T)`, application left-associative. `|t|` = number of S-leaves.
Reduction `→`: contract any redex `S x y z → x z (y z)`. Every S-term has the spine form
`t = S a1 … ak`; we write `ch(t) = [a1,…,ak]` and `t = S·ch(t)`.
A **head normal form (hnf)** is a term with k ≤ 2: `S`, `S a`, `S a b`. Head reduction contracts the
spine redex `S a1 a2 a3` when k ≥ 3.

---------------------------------------------------------------------------------------------------
## Lemma 1 (leaf monotonicity) — PROVED
If `t → t'` then `|t'| = |t| + |z| − 1 ≥ |t|` where z is the third argument of the contracted redex.
*Proof.* `|S x y z| = 1+|x|+|y|+|z|`, `|x z (y z)| = |x|+|y|+2|z|`. ∎
Corollary: no S-term behaves as I or K (`M x →* x` impossible), the classical obstruction.

## Lemma 2 (head machine; compositionality) — PROVED
(a) For `k ≥ 3`, the head step is `S a1 a2 a3 a4…ak → S ch(a1) a3 (a2 a3) a4 … ak`; as lists
`[a,b,c]++R ⇒ ch(a)++[c, b·c]++R` (`b·c` = b with c appended to its argument list).
(b) Let `H(t)` be the hnf reached by head reduction (⊥ if none). Then
`H(S)=S`, `H(t1 t2) = App(H(t1), t2)` (⊥ if H(t1)=⊥), where for an hnf h:
`App(S,v)=S v`, `App(S p,v)=S p v`, `App(S p q, v) = App(App(H(p),v), q v)`.
(c) For a list P with |P| ≥ 3 and any R: head reduction of `S·(P++R)` first performs exactly the head
reduction of `S·P`; if that has no hnf, neither has `S·(P++R)`; otherwise it continues from `H(S·P)++R`.
*Proof.* (a) definition. (c) the head step only reads the first three list entries; induction on steps.
(b) is (c) unfolded; for `App(S p q, v)`: `S p q v → p v (q v)` and by (c) the head reduction of
`p v (q v) = S·(ch(p)++[v, q v])` first head-normalises p, then the triple, then appends `q v`. ∎
Standard fact used: t has an hnf (t →* some hnf by any reduction) iff head reduction of t terminates
(standardisation for orthogonal CL; internal steps never change the spine length k ≥ 3 and commute with
the head step by the parallel-moves lemma).

## Lemma 3 (finite models are conversion invariants) — PROVED
Let `(M,·)` be a magma with `s ∈ M` such that `s·x·y·z = x·z·(y·z)` for all `x,y,z ∈ M`
(an *S-model*). Define `[S]=s`, `[t u]=[t]·[u]`. If `t →* t'` then `[t]=[t']`.
*Proof.* One step: the redex evaluates to `s[x][y][z] = [x][z]([y][z])`, and `·` is a function, so
replacing a subterm by one with the same value preserves the value of the whole. Induct. ∎

## Lemma 4 (all head-unstable terms are one syntactic class) — PROVED (sketch to be written in full)
If t, t' both have no hnf then for every one-hole context C: `C[t]` has an hnf ⟺ `C[t']` has an hnf.
*Proof sketch.* Run the head machine on `C[t]` and `C[t']` in lockstep. Steps only open the *top* list
entry; an entry equal to t (or t') is never inspected until it is opened. If an occurrence of t is ever
opened, Lemma 2(c) with `P = ch(t)` (no hnf, |P| ≥ 3) shows that run diverges, and the same happens at
the same moment in the other run. If no occurrence is ever opened, the two runs are identical up to the
substitution t ↦ t', hence terminate together. ∎  (Consistent with M35: ⊥ is a single class.)

---------------------------------------------------------------------------------------------------
## Theorem A (no-hnf certificate) — PROVED, relying on a COMPUTATIONALLY CERTIFIED finite check
**Novelty: NOT new.** M35 is isomorphic to the automaton of BEKW Fig. 14 (EXPERIMENTS E8), and BEKW already
observe that it is a model, so this direction is known; included for completeness/reproducibility.
Let `M35` be the 35-element magma in `data/model35_hn.txt` (s = class 0), F its 34 classes marked HN=1,
⊥ = class 33. Finite facts checked by `code/verify_model.py`:
 (i) `s·x·y·z = x·z·(y·z)` for all 35³ triples; (ii) `s, s·x, s·x·y ∈ F` for all x, y.
Then: **if `[t] = ⊥` then t has no head normal form.**
*Proof.* If `t →* h` with h an hnf then `[t]=[h] ∈ {s, s·[a], s·[a]·[b]} ⊆ F` by Lemma 3 and (ii). ∎
Corollary: `[t]=⊥` ⇒ t has no normal form and its Böhm-tree root is ⊥; checkable in linear time.

## Theorem B (exhaustive classification up to 19 leaves) — COMPUTATIONALLY CERTIFIED
**Novelty: verification of BEKW Question 10 for |t| ≤ 19; the 2n−5 bound/extremal family may be new (minor).**
For every S-term t with `|t| ≤ 19` (654,960,000+ terms):
 t has an hnf ⟺ `[t]_{M35} ∈ F`; and if it has one, head reduction reaches it in at most
 `max(16, 2|t|−5)` steps (the bound 2n−5 is attained for every n=10..19 by `S(SS)(S^{n-6})SSS`,
 where `S^k` is the left-assoc chain of k S's).
*Proof.* Census (`sterm.exe verify`, data/ver_n.txt): every term with class in F was head-reduced and
reached an hnf within the stated number of steps (explicit computation); every term with class ⊥ has no
hnf by Theorem A. ∎   [Reproduce: `sterm.exe verify n lo hi ../data/model35_hn.txt 400 out` for n ≤ 19.]

---------------------------------------------------------------------------------------------------
## Conjecture C1 (= BEKW Question 10) — PROVED 2026-10-25 as Theorem Q10 below (pending independent audit); decidability of head normalisation was already a theorem of Padovani (Satellite Ch. 7, proof not read)
For all S-terms t: t has an hnf ⟺ `[t]_{M35} ∈ F`. (⇐-direction of failure = Theorem A.)
Consequence: head normalisation of S-terms is decidable in linear time.

## Theorem Q10 (BEKW Question 10 holds) — PROVED (elementary argument + COMPUTATIONALLY CERTIFIED finite facts; independently audited) and MACHINE-CHECKED in Lean 4 (lean/Q10.lean, 2026-10-27)
*Lean (main agent, 2026-10-27).* `Q10 (t : Tm) : (∃ n L', run n (args t) = some L' ∧ L'.length ≤ 2) ↔ isF (cls t) = true`:
head reduction of t terminates iff its M35 class is in F. Axioms: propext, Classical.choice, Quot.sound; no sorry.
The proof follows the four steps below on the head machine itself, with no separate big-step semantics. A mutual
well-founded recursion `hnfF` / `chainF` is ordered by the lexicographic measure (8 − rank, call kind,
tail-chain-graph index, size). `hnfF` splits off the last argument; rank rises, or the size falls at the self-loop
12·s = 12. `chainF` treats p = S, peel (index falls, or size falls at the one peel self-loop) and refill (the sub-run on
p·v at strictly higher rank, since the multiplier q·v ≠ s; then the index falls; q′ is an application by `run_form`).
The finite facts are seven Boolean checkers evaluated by the KERNEL (`decide +kernel`) over a base-35 bignum
encoding of M35 and of the 8,329-state index table:
* (F2) no product is s;
* not-F is left-absorbing;
* the rank law with the single self-loop 12·s;
* the PRE class set (terms with ≥ 2 arguments; the over-approximation 'any a ≠ s' is NOT acyclic);
* completeness of the peel and decomposition tables;
* the index strictly decreases on all 84,205 edges except the one peel self-loop.

`k1` uses no axioms; the others use propext. Tables: code/q10_lean_facts.py, data/q10_tables_PRE.txt.
_Audit 4 (2026-10-25, adversarial subagent, own code): correct; no counterexample, no missing edge; four small gaps in the
write-up repaired below (rank definition, Step 1 direction, existence of H(p_i) in the refill case, (F4) citation)._
**Statement.** For every S-term t: t has a head normal form ⟺ [t]_{M35} ∈ F.
*Finite facts* (code/verify_model.py, code/q10_chaincert.py; re-run 2026-10-25):
 (F1) M35 is an S-model; S, S x, S x y always land in F; ⊥ = class 33 is left-absorbing (Theorem A).
 (F2) **Lemma 15:** no product α·β equals s = [S]. Hence a term has class s iff it is the term S.
 (F3) The right-multiplication graph α → α·β minus self-loops is acyclic; the only self-loop at an F class is 12·s = 12.
      Every class reaches ⊥ in it (checked); rank(α) := length of a longest path from α to ⊥ (≤ 8).
 (F4) The tail-chain graph G defined in Step 3 (8,329 states, 84,206 edges) has no directed cycle other than self-loops,
      and none of its refill edges is a self-loop (networkx in q10_chaincert.py; independent Tarjan in refillgraph.py;
      audit 4 re-derived it with Tarjan, Kahn and networkx on its own edge set: 7,380 peel + 76,826 refill edges).
*Step 1 (big-step evaluation).* By Lemma 2(b),(c) head normalisation is the recursive procedure
H(S) = S, H(t1 t2) = App(H(t1), t2), App(S, v) = S v, App(S p, v) = S p v, App(S p q, v) = App(App(H(p), v), q v),
each equation of which is a valid reduction, so a call H(t) that returns yields a reduct of t that is an hnf. Suppose
[t] ∈ F and t has no hnf; then H(t) does not return. Give every call a result class: [t] for H(t), [h]·[v] for
App(h, v). The calls that never return form an infinite path from the root (each call makes at most three subcalls in
sequence, so a non-returning call has exactly one non-returning subcall; App(S, v) and App(S p, v) make none).
*Step 2 (rank).* Let [t] ∈ F. Along the path a tail subcall (H(t1 t2) → App(H(t1), t2), App(S p q, v) → App(h′, q v))
has its parent's class; a non-tail subcall has a class κ from which the parent's class arises by right multiplications:
H(t1) by ·[t2]; H(p) by ·[v]·[q v] (S-identity); App(H(p), v) by ·[q v]. So all classes on the path are in F (⊥ is
left-absorbing), rank never decreases along the path, and it increases at a non-tail step unless every multiplication
is the self-loop 12·s. By (F2) a multiplication by [q v] is never by s, so the only rank-preserving non-tail steps are
H(t1 S) → H(t1). Since rank ≤ 8, from some call on the path consists of finitely many steps H(t1 S) → H(t1) (each to a
proper subterm), at most one step H(t1 t2) → App(H(t1), t2), and then App tail calls only. (This sharpens Lemma R:
case (B) cannot occur.)
*Step 3 (tail chains).* Hence a counterexample yields calls App(S p_i q_i, v_i), i ≥ 0, with
S p_{i+1} q_{i+1} = App(H(p_i), v_i) = H(p_i v_i) and v_{i+1} = q_i v_i, all with class ρ = [S p_i q_i v_i] ∈ F. By the
spine of p_i:
 – p_i = S: App(S, v_i) = S v_i has one component, so the next call returns — impossible in an infinite chain;
 – p_i = S x (**peel**): H(p_i) = S x, so p_{i+1} = x, a proper subterm of p_i, and q_{i+1} = v_i;
 – p_i has ≥ 2 arguments (**refill**): the subcall H(p_i) returned, and its value has two components (a term with ≥ 2
   arguments only reaches two-component hnfs, see next sentence), say H(p_i) = S x y; S p_{i+1} q_{i+1} is the hnf of
   S x y v_i, a term with three arguments. The configuration after any head step has length |ch(a)| + 2 + |R| ≥ 2, so the final one is [c, b·c] (with
   ch(a) and R empty): q_{i+1} = b·c is an application and, by (F2), [q_{i+1}] ≠ s.
With (a_i, b_i, β_i) := ([p_i], [q_i], [v_i]), a peel is an edge (a, b, β) → (x, β, b·β) with s·x = a, and a refill is an
edge (a, b, β) → (a′, b′, b·β) with a ∈ {s·x·y}, a ≠ s, s·a′·b′ = a·β and b′ ≠ s. G is the graph of all these edges on
the states (a, b, β) with s·a·b·β ∈ F (ρ is invariant along both kinds of edges by the S-identity).
*Step 4 (conclusion).* The chain's state sequence is an infinite walk in G. By (F4) it is eventually constant, and from
then on every step is a self-loop, hence (no refill self-loops) a peel; but consecutive peels pass to proper subterms of
p_i, so there are only finitely many. Contradiction. Hence every t with [t] ∈ F has an hnf; with Theorem A, the
statement. ∎
*Validation.* Every one of the 15,923 tail-chain transitions in head runs of F terms with ≤ 12 leaves is an edge of G of
the right kind (code/q10_chaincert.py, part (3)); audit 4 checked 2,614,659 transitions (all 290,512 terms ≤ 13 leaves)
and 2,420,727 more on 164,416 random/adversarial F terms with 20–60 leaves (all head-normalised, slowest 111 steps =
2n − 5 at 58 leaves), 0 missing edges. *Corollary (audit 4):* the longest path in G has 13 edges and at most 2 refills,
so every tail chain has at most 2 refills (observed in code/tailchain.py).
*Consequences.* (i) Head normalisation of S-terms is decidable in linear time (a bottom-up pass over the 35 × 35 table) — an
independent proof of Padovani's theorem (whose proof we have not seen; his chapter may contain this or another argument).
(ii) R10′ (head normalisation cannot compare counts or count mod p) becomes unconditional. (iii) Propositions Q and Q′
become unconditional: every term with an F_P class is productive (soundness half of C6) and every term outside F_fin has
an infinite Böhm tree (one half of C8). (iv) Lemma 13, Proposition T's search and C12 lose their role as Q10 tools.
*Why earlier attempts missed it.* The abstract call graph on pairs App(h-class, v-class) has cycles; they disappear on
triples (a, b, β) once peels (syntactic, structurally decreasing) are separated from refills and the refill's second
component is known not to be S (Lemma 15).

## Proposition Q″ (the "infinite" verdicts of the leftmost- and rightmost-path models are correct) — PROVED (uses Theorem Q10) and MACHINE-CHECKED in Lean 4 (lean/PathModels.lean, 2026-10-27)
*Lean (main agent, 2026-10-27).* `propQ2Lft` / `propQ2Rgt`: if the L36 (resp. R19) class of t is flagged, then for every
depth d the leftmost (resp. rightmost) Böhm-tree path has d further nodes, each with a head normal form (`InfLft` /
`InfRgt`). Built on the machine-checked Q10. The model facts (S-identity, closure of the flag, the joint sub-magmas with
M35 of 69 resp. 78 elements, with no flagged hnf-free pair) are kernel-checked; generator code/gen_path_models.py.
Axioms: propext, Classical.choice, Quot.sound.
*Certified facts (2026-10-25):* the 36-class leftmost-path model L36 and the 19-class rightmost-path model R19 are
S-models (0 violations); flag(S) = 0; flag(s·x) = flag(x); flag(s·x·y) = flag(x) for L36 and = flag(y) for R19; in the
sub-magma of (model × M35) generated by S (69 resp. 78 elements) no element pairs flag 1 with ⊥_M.
*Claim.* If [t]_{L36} has flag 1, the leftmost path of BT(t) is infinite (and every node on it has an hnf); likewise for
R19 and the rightmost path. *Proof.* The joint fact gives [t]_M ∈ F, so t has an hnf h by Theorem Q10; [h] = [t] (Lemma 3),
h ≠ S (flag(S) = 0), and the closure facts give the first (resp. last) component of h flag 1. Iterate. ∎
The other halves (flag 0 ⇒ the path is finite) remain open; they are certified by census for all terms ≤ 16 leaves (E26).

## Lemma P (descent lemma) — PROVED (independently audited, audit 5: correct; presentation fixed) and MACHINE-CHECKED in Lean 4 (lean/LP1.lean, 2026-10-27)
*Lean (main agent, 2026-10-27), contrapositive form:* `lemmaP : run N (L ++ [A, B]) = some H → H.length ≤ 2 → LeftEnd L`
(if S·L·A·B has a head normal form, the leftmost path of S·L ends at the leaf S), by strong induction on N with the
lemma `run_prefix_hnf` (a run with material appended reaches an hnf only after its prefix did, in no more steps).
Axioms: propext, Quot.sound.
If the leftmost Böhm-tree path u_0 = t, u_1, … of a closed S-term t does **not end at the leaf S** — i.e. it is infinite,
or it reaches a node without hnf — then t A B has no head normal form, for all terms A, B (closed or open; variables are
stuck heads, which the argument never reaches).
*Proof.* Use the big-step equations of Lemma 2(b), extended to open terms by H(x·args) = x·args and
App(x·args, v) = x·args v for a variable x (Lemma 2(c) and "hnf ⇔ head reduction terminates" hold unchanged). Write
E_j(w, w′) for the computation of App(App(H(u_j), w), w′); H(t A B) = E_0(A, B). If u_j has no hnf, E_j already diverges. If H(u_j) = S u_{j+1} y, then App(S u_{j+1} y, w) = App(App(H(u_{j+1}), w), y w),
so E_j(w, w′) contains E_{j+1}(w, y w) as a proper sub-computation. If H(u_j) = S u_{j+1}, then App(S u_{j+1}, w) = S u_{j+1} w
and App(S u_{j+1} w, w′) = App(App(H(u_{j+1}), w′), w w′) = E_{j+1}(w′, w w′), again a proper sub-computation. If E_0 terminated,
the step counts would decrease forever: with h_j = H(u_j), (w_0, w′_0) = (A, B) and the next pair (w, y_j w) resp.
(w′, w w′), let N_j be the number of head steps of h_j w_j w′_j and K_{j+1} that of u_{j+1}; then
N_j = 1 + K_{j+1} + N_{j+1} + r_j with r_j ≥ 0 (r_j = 0 in the one-component case), so N_j > N_{j+1}. If the path reaches a
node u_m without hnf, E_{m−1} must compute H(u_m), which diverges. Nothing is assumed about A, B. ∎ (Audit 5 checked the
recursion with variable clauses against the head machine on 59,624 probe runs and the step identity on 33,687 descent
steps.)
*Class bookkeeping (for later use).* [E_j] = [E_{j+1}] in the one-component case and [E_j] = [E_{j+1}]·[w′] in the
two-component case.

## Theorem LP1 (outside the five D2 classes, leftmost paths end at the leaf S) — PROVED (Lemma P + Theorem Q10 + a finite check; audited, audit 5) and MACHINE-CHECKED in Lean 4 (lean/LP1.lean, 2026-10-27)
*Lean:* `LP1 (t) (hF : isF (cls t) = true) (hD : cls t ∉ [24, 26, 28, 31, 34]) : LeftEnd (args t)`. The class
representatives of data/model35_hn.txt (kernel check `kreps`) and the D2 characterization (`kd2`) are kernel-checked;
generator code/gen_lp1.py. Axioms: propext, Classical.choice, Quot.sound.
Let D2 = {α ∈ F : α·β·γ = ⊥ for all β, γ} = {24, 26, 28, 31, 34} (M35; recomputed by audit 5; the same with β, γ ∈ F). If
[t]_{M35} ∈ F ∖ D2, the leftmost path of BT(t) is finite and ends at the leaf S; if [t] = ⊥ it ends at the root. *Proof.* Pick classes β, γ with [t]·β·γ ∈ F and closed terms A, B in them (all 35 classes are generated by S); t A B has
an hnf by Theorem Q10, so by Lemma P the path ends at the leaf S. ∎ (Audit 5: no term in F ∖ D2 up to 13 leaves has a path
ending elsewhere.) *Consistency check:* the joint classes of L36 × M35 with flag 1 are (9, 28) and (10, 26), both inside D2.
**Remaining obligation for the leftmost-path model:** flag 0 ⇒ finite for the 18 flag-0 joint classes inside D2:
(14,28), (14,24), (14,26), (14,31), (21,26), (16,24), (15,26), (25,26), (32,26), (22,26), (16,26), (14,34), (16,31),
(28,26), (11,26), (33,24), (17,26), (33,26). There closed probes are useless (every t A B is ⊥). Open probes t z z can at best certify "the path ends at S" (Lemma P:
paths ending in ⊥ make every probe diverge), and they fail even for some S-ending paths (e.g. S(SS)S(S(SSS)S), class
(14,28)); paths ending in ⊥ are common in (14,26) and (14,28) (26,558 and 17,591 terms up to 13 leaves, audit 5) — so the
remaining obligation needs a direct size-change argument on the leftmost walk (see 'Reload cycles' below), not a probe.

## Reload cycles in the resisting component (2026-10-25) — analysis; the measure is OPEN
*Exact mechanism of an infinite leftmost path (PROVED by direct computation for every k; smallest example
S(S(SS))(S(SS))(SS)S, joint class (9,28)).* Let B = S(SS)(SS) and N_k = (SS)^k B. Head reduction gives the leftmost steps
 N_i N_k S ↦ N_{i−1} N_k S (i ≥ 1, countdown) and B N_k S ↦ N_k N_{k+1} S (reload), because
 B N S = S(SS)(SS) N S → … → S (N (SS N) S) (S N … ) — B is a "reloader": B N S has first component N (SS N) S.
The node sequence is (i, k) = (0,1), (1,2), (0,2), (2,3), (1,3), (0,3), (3,4), …: the second slot grows at every reload, so no
size-change thread decreases infinitely often — the signature of an infinite path.
*Finite counterpart.* S S N X Y (X = S(SS), Y = SS(S(SS)), class (14,28)) counts N down and never reloads; the quadratic
family t_k of Proposition S reloads with a strictly smaller outer counter each time (k + 1 rounds).
*What a proof must show.* On leftmost walks inside {(14,28), (14,26)} (the only component whose cycles contain
size-increasing steps), every infinite sequence of size-increasing steps has a slot thread that strictly decreases
infinitely often (size-change termination). Observed transitions between consecutive size-increasing nodes in (14,28)
(1,869 over ≤ 11 leaves + 25,000 random terms) mix a decreasing slot with copied and growing slots, e.g.
(e0, e1, e2) ↦ (e1, e1, ⊂e0, ⊃e1); so no single quantity works (node size fails 698/1,700 times; the multiset of
argument sizes between consecutive growth points fails 73/82 times) — the certificate has to follow threads.
*Counterexample search (no large enumeration).* 49,726 counter-shaped candidates (SS)^j B M R, S S K M R, S K M R with
parts of ≤ 5 leaves: 14,122 lie in flag-0 D2 classes; every leftmost walk ends (at S: 6,575; in ⊥: 7,547) within 18
nodes. No indefinite reloading found.
*Next step.* A symbolic transition abstraction for the walk (slots with joint classes; opening a slot reveals its spine
sub-slots, all strictly smaller; composites b·c tracked as sums), its size-change graphs, and the Lee–Jones–Ben-Amram
closure test; the abstraction is to be checked by the same single auditor before any consequence is promoted. Census (code/probe.py, ≤ 10 leaves; audit 5 to 13 leaves): every term with an infinite leftmost path has a diverging
probe; paths ending at S have converging probes except 6, 45, 286, 1450, 6659 terms at 9–13 leaves (all in (14,28) or
(14,26)); paths ending in ⊥ always diverge (now a theorem: Lemma P).
*Attempted certificates for those halves (2026-10-25, code/btpathcert.py, leftpathcert.py, pathcert2.py).* Splitting
Böhm-tree steps into structural ones (child = proper subterm) and computed ones (node with ≥ 3 arguments, hnf
S v_k (q_k v_k) from its final tail chain) does not give an acyclic abstraction: for L36 the only bad strongly connected
component is {(14, 28), (14, 26)} (joint L36 × M35 classes), but refining states by the classes of the parts of composite
nodes does not remove it, and concrete leftmost paths from these classes really take up to 5 size-increasing steps
(e.g. S(S(SS(SS(SS(SS(SSSS))))))S(SS): new, dec, new, dec, …), driven by a nested SS(·) counter — a proof needs a measure
for that counter. For R19, B131 and P39 the coarse abstraction has larger bad components (20, 37, 17 classes).

## Conjecture C2 (fast-or-never) — CONJECTURAL, strongly supported
If t has an hnf, head reduction reaches it within `2|t|` steps (Theorem B: holds for |t| ≤ 19).

### Partial reduction of C1 (PROVED parts, remaining obligations explicit)
*Rank.* In M35 the right-multiplication graph `α → α·β` has no cycles except the self-loops at
class 12 (`SS(S(SS))`) and at ⊥ (`code/callgraph.py`, rank listing). Define rank(α) = longest path to ⊥
ignoring self-loops (rank(s)=8).
*Call tree.* Executing H/App of Lemma 2(b) gives a call tree; a call H(t) has result class [t], a call
App(h,v) has result class [h]·[v]. Tail subcalls (`H(t1 t2) → App(H(t1),t2)`,
`App(S p q,v) → App(w, q v)`) keep the result class; the non-tail subcalls (`H(t1 t2) → H(t1)`,
`App(S p q,v) → H(p)`, `App(S p q,v) → App(H(p),v)`) have a result class from which the parent's is
reached by 1–2 right multiplications, hence strictly larger rank unless every multiplication is the
self-loop at 12. If the root's class is in F, every call on a diverging path has class in F (⊥ left-absorbing).
*Lemma R (PROVED).* If t has class in F and no hnf, the call tree has an infinite path whose result
class is eventually constant ρ ∈ F, and either
 (A) the path eventually consists only of App tail calls `App(S p_i q_i, v_i) → App(hnf(p_i v_i), q_i v_i)`, or
 (B) ρ = class 12 and the path contains infinitely many non-tail self-loop steps.
(Proof: rank ≤ 8 never decreases along the path; H→H steps descend the finite left spine.)
*Remaining obligations.* Rule out (A) and (B).
 - A finite abstraction by classes alone CANNOT do it: the abstract call graph has cyclic SCCs (one of
   size 51 around class 12; tail self-loops at App(26,16), App(24,16)), and terminating runs really do
   contain tail chains of length ≈ |t|−3 with repeated abstract states (`code/bigstep.py`).
 - Observed mechanism (EXPERIMENTALLY SUPPORTED): in a tail chain, whenever H(p_i) = S x the next first
   component is x (one `S(…)` layer peeled, Lemma 2(a): `[S x, q, v] ⇒ [x, v, q v]`); chains are long only
   while the first component is a deep `S(S(…))` nest; refills of the first component (H(p_i) two-component,
   or promotion of the argument via class-12 terms `App(S S X, v) = S v (X v)`) are what a proof must bound.
   Candidate measure: lexicographic (rank of nested-call classes, structural size of the current first
   component), with refills charged to strictly-higher-rank nested calls.

---------------------------------------------------------------------------------------------------
## Lemma 5 (Fibonacci peeling) — PROVED
Nests: `N_0 = S`, `N_{j+1} = S N_j`. For all S-terms q, v and all j ≥ 0:
`S N_j q v  →^{j+1}  S F_{j+1} F_{j+2}` (head steps), where `F_0 = q, F_1 = v, F_{i+2} = F_i F_{i+1}`.
More generally, for any base z: `S (S^{(j)} z) q v →^{j} S z F_j F_{j+1}` with `S^{(j)} z` = j-fold `S(…(S z))`.
*Proof.* Head machine (Lemma 2a): `[S x, b, c] ⇒ [x, c, b c]`, so `[S^{(j)} z, F_0, F_1] ⇒ [S^{(j-1)} z, F_1, F_0 F_1]
= [S^{(j-1)} z, F_1, F_2] ⇒ … ⇒ [z, F_j, F_{j+1}]` (induction on j). For z = S: `[S, F_{j}, F_{j+1}] ⇒ [F_{j+1}, F_j F_{j+1}]`. ∎
Spine form of the words: `F_{2m} = q F_1 F_3 ⋯ F_{2m-1}`, `F_{2m+1} = v F_2 F_4 ⋯ F_{2m}` (induction).
Consequences: BT(S N_j q v) = S(BT(F_{j+1}), BT(F_{j+2})); in any finite S-model the class sequence
([F_i]) is eventually periodic (pair recurrence), so every regular conversion-invariant property is
eventually periodic in j along such families — the basis of the non-regularity test for C3.

---------------------------------------------------------------------------------------------------
## Theorem C (an S-term with a non-regular Böhm tree) — PROVED (novelty unknown; check Satellite Ch. 7)
Let `N_0=S, N_{j+1}=S N_j` (so N_1=SS, N_3=S(S(SS))), `K = S S N_3 N_1` (= SS(S(S(SS)))(SS), 8 leaves),
`W_0 = K`, `W_{m+1} = S S W_m`. Head-reduction facts (all by the head machine, Lemma 2a):
 (i)  `K Z →³ S P (Z P)` with `P = N_3 N_1 Z`                 ([S,N3,N1,Z] ⇒ [N1,N3N1,Z] ⇒ [S,Z,N3N1Z] ⇒ [P, Z P])
 (ii) `N_3 N_1 Z →³ S (Z (N_1 Z)) ((N_1 Z)(Z (N_1 Z)))`         ([N2,N1,Z] ⇒ [N1,Z,N1Z] ⇒ [S,N1Z,Z(N1Z)] ⇒ …)
 (iii) `W_m Y →¹ S Y (W_{m-1} Y)` for m ≥ 1                     ([S,W_{m-1},Y] ⇒ [Y, W_{m-1}Y])
 (iv) `K →¹ S N_1 (N_3 N_1)`, a normal form; hence every W_m is normalising, `|nf W_m| = |nf K| + 2m = 9 + 2m`.
With `N_1 W_r = W_{r+1}`, the Böhm tree of `K W_r` (r ≥ 1) contains the path
 `K W_r →₁ P_r →₁ W_r W_{r+1} →₂ W_{r-1} W_{r+1} →₂ ⋯ →₂ W_1 W_{r+1} →₂ K W_{r+1}`
(→₁/→₂ = first/second hnf component), and at node `W_r W_{r+1}` the first component is `W_{r+1}`.
Hence the subtree of BT(K W_r) at address (1,1,1) is the finite tree nf(W_{r+1}) of size 11+2r, so the
trees BT(K W_r), r ≥ 1, are pairwise distinct; BT(K W_1) contains all of them as subtrees.
**Therefore BT(K W_1) (an 18-leaf term) has infinitely many distinct subtrees: Böhm trees of S-terms are
not regular in general.** The 10-leaf term `SS(SS)(S(S(SS)))(SS)` has BT(K W_1) as a subtree (its BT path
reaches K W_1 at depth 1). This upgrades R6 from EXPERIMENTALLY SUPPORTED to PROVED.
Interpretation: a self-incrementing unary counter; round r has r+2 nodes and emits the finite garbage
W_{r+1} sideways at each decrement — the "BT-spine computation with garbage emission" mechanism.

---------------------------------------------------------------------------------------------------
## Lemma 6 (iterator lemma) — PROVED
Wrappers: `V_0 = B`, `V_{m+1} = S U V_m`, i.e. `V_m = (S U)^m B` (m-fold application of `S U`); W-family: U = S.
 (a) `V_m x →¹ U x (V_{m-1} x)`, hence `V_m x ↠ (U x)^{(m)}(B x)` (m-fold nested application of `U x`).
 (b) `W_k c →¹ S c (W_{k-1} c)` (k ≥ 1): every applied W-wrapper is a right comb with identical teeth c
     ending in `B c`; `W_k x y ↠ (x y)^{(k)}(B x y)` (iterator / Church-numeral behaviour).
 (c) In the head machine, opening `W_k c⃗` (k ≥ 1) with (x,y) gives `[c1, W_{k-1}c1, c2,…,cr, y, x y, …]`
     in 2 steps: the depth is only ever *decremented by one per opening*.
*Proof.* One S-step each (`S U V x → U x (V x)`; `S S W c → S c (W c)`), and induction on m. ∎

## Theorem E (counter-freeness of the 35-state recognizer) — status corrected 2026-10-25
**E-alg (unconditional finite-algebra fact, COMPUTATIONALLY CERTIFIED twice, independent code on M35 and on the
published BEKW Fig. 14 table):** items (i)–(ii) below.
**E-hn (statement about actual head normalisation): now UNCONDITIONAL — the BEKW recognizer is correct (Theorem Q10).**
(Before Theorem Q10 only the *no-hnf* half (E1 second sentence) was unconditional, because it uses Theorem A alone.)
Finite facts (code: inline scripts recorded in EXPERIMENTS E13; checked on M35 and independently on the
published BEKW Fig. 14 table):
 (i) for every φ, β ∈ M35 the left orbit `β, φβ, φ(φβ), …` is constant from step 5 on (fixed point,
     cycle length 1 for all 1,225 pairs); for φ = s·u (wrappers) it is constant from step 2 on;
 (ii) the context monoid of M35 (maps x ↦ C̄(x) generated by x ↦ a·x, x ↦ x·a) has 460 elements and is
     **aperiodic**: f⁶ = f⁷ for every element f (21 idempotents).
Consequences (PROVED from (i),(ii) + Lemma 3 + Theorem A):
 (E1) For all contexts P, E and terms D: `[E[P^k[D]]] = [E[P^6[D]]]` for all k ≥ 6. In particular, if
      `E[P^6[D]]` has no hnf then no `E[P^k[D]]` (k ≥ 6) has one.
 (E2) Iterates: `[C[f^k(s)]] = [C[f^5(s)]]` (k ≥ 5) for all f, s, C; wrappers: `[C[V_m]] = [C[V_2]]` (m ≥ 2).
 (E3) [E-hn, PROVED via Theorem Q10] head-normalisability
      along any pumping family is constant from k = 6, along iterates from k = 5, along wrappers from m = 2.
      Hence no head-normalisation test can compare two counts (no "j ≤ k" pattern) or count modulo p:
      the zero-counter principle holds for head normalisation (the BEKW recognizer is correct by Theorem Q10).
Novelty: aperiodicity of the BEKW automaton's context monoid is not stated in BEKW; status in Padovani's
chapter unknown.

## Conjecture C4 (Böhm-tree finiteness is counter-free) — REFUTED by Theorem P2 (kept for the record)
For all contexts P, E and terms D, BT-finiteness of `E[P^k[D]]` is eventually constant in k with a uniform
small threshold (data: ≤ 4 on 3,248 pumping sequences; ≤ 2 on 17,091 wrapper sequences; all 6,254+
two-counter grids eventually constant in each coordinate, E10–E12). Would follow from a finite S-model for
BT-finiteness with aperiodic context monoid (open, NEXT_STEPS).
*On "keeping two values":* any subterm can be carried passively across a round (e.g. inside the base or
the argument Y of Lemma 6(b)), so keeping values is trivial; the obstruction is *testing* them — every
test available through head normalisation is counter-free (Theorem E), and conjecturally so are
Böhm-tree-finiteness tests (C4).

---------------------------------------------------------------------------------------------------
## Proposition F (an explicit S-only counter) — PROVED
Fix any closed S-term Y (the *handler*). Define `D_0 = S Y`, `D_{k+1} = S S Y D_k` (= (SSY)·D_k).
 (rep)  D_k is defined uniformly for all k ∈ ℕ.
 (inc)  D_{k+1} is the application of the fixed term `S S Y` to D_k.
 (dec)  `D_{k+1} →¹ S D_k (Y D_k)` (head machine: `[S, Y, D_k] ⇒ [D_k, Y D_k]`): the head normal form has
        exactly two components, the first being D_k, the second the handler applied to the predecessor.
 (zero) `D_0 = S Y` is already a head normal form with exactly one component.
Admissible observation: the number of components of the head normal form of a node (decided by ≤ 1 head step)
is 2 iff the counter is nonzero. Along the leftmost Böhm-tree path, D_k ↦ D_{k−1} ↦ … ↦ D_0 ↦ Y, reading k in
unary; along "last component", D_{k+1} ↦ Y D_k (handler regains control with the predecessor as data).
*Proof.* One head step each (Lemma 2a). ∎

## Lemma 7 (order and bottom principles of the head machine) — PROVED
In a step `[a,b,c]++R ⇒ ch(a)++[c, b·c]++R`:
 (i)  a compound is only ever formed as `b·c` with b *above* c (an element can only absorb elements below it);
 (ii) the element at position c survives unchanged (a clean copy) and moves up to position |ch(a)|;
      the element at position b is never seen again except as the head of `b·c` ("pollution");
 (iii) the last element of the list changes only by `last := b·last`; hence in a terminating run the final
      hnf `S p q` has q (or p) of the form `b_k(b_{k−1}(…(b_1 e_last)…))`: information from the top reaches the
      bottom of the next node only as *heads* of compounds, while the original last element stays innermost.
 (iv) opening an element pushes its children *above* everything: an opened datum's components are in
      control of (can only absorb) the elements below them.
*Proof.* Immediate from the rule; (iii) by induction on steps. ∎

## Observation H (inspection obstruction) — COMPUTATIONALLY CERTIFIED for small gadgets
With x, w opaque (never opened): for every code element g ≤ 8 leaves, the head run of `S g x w` terminates only
for the nests g = N_j (Fibonacci peeling), and then x occurs only as the *head* of compounds (in control); for
every g1, g2 ≤ 6 leaves (4,225 pairs) and every g1,g2,g3 ≤ 4 leaves, the head run of `S g1 … gj x w` (j = 2, 3)
never reaches a head normal form without opening x or w (code/symb.py). Consequence for counters: a predecessor
exposed inside a head run cannot be handed back to code as clean data within the same run (for these gadget
sizes); every decrement either cascades (iterator) or is completed at a Böhm-tree fork.

## Proposition G (pushdown discipline of fork-decrements) — PROVED (for the representation of Prop. F and any
representation where a decrement is completed at a Böhm-tree fork)
If a node is a closed counter term C and its decrement is the fork `C →* S C' (Z C')` (or similar), the
continuation along the path is a component of hnf(C), hence a term built only from subterms of C and
S-applications: the post-decrement configuration is a function of C alone. Information created after C was
built (e.g. a second counter changed since) cannot reach the continuation. Thus fork-decrements realise a
last-in-first-out store whose records are fixed at push time (pushdown discipline), not a register machine.

---------------------------------------------------------------------------------------------------
## Theorem H (uniformity / inspection principle) — PROVED (uses only Theorem A and certified finite facts)
Let T[x1..xk] be an S-term with opaque variables. Write T̂ : M35^k → M35 for its polynomial in M35.
 (a) If the head run of T reaches a head normal form without opening any xi, then T̂(α) ∈ F for every α ∈ M35^k.
 (b) If moreover that run ends in `S P1 P2` (resp. `S P1`, `S`), then T̂ ≡ (S P1 P2)^ (resp. …) identically on M35^k;
     more generally every symbolic reduction T[x⃗] →* T'[x⃗] that never opens a variable forces T̂ ≡ T̂' on every
     finite S-model.
*Proof.* A run that never opens xi performs the same steps after substituting arbitrary closed terms Xi for xi,
so T[X⃗] has an hnf for all X⃗; by Theorem A (contrapositive) its class is in F. Every class of M35 is inhabited
(S generates M35), so (a) follows; (b) is Lemma 3 applied to every substitution instance. ∎
**Corollary H1 (no clean holding — all gadget sizes).** For every closed S-terms g1, g2 (and g1, g2, g3) and
opaque x, w, the head run of `S g1 g2 x w` (resp. `S g1 g2 g3 x w`) opens x or w, or diverges.
*Proof.* Finite check (inline script, EXPERIMENTS E16): for every (γ1,γ2) ∈ M35² (all 1,225) — and every triple
(all 42,875) — some (ξ,ω) gives `s γ1 γ2 ξ ω = ⊥` (resp. `s γ1 γ2 γ3 ξ ω = ⊥`); apply Theorem H(a). ∎
For one code element (`S g x w`) the classes escaping the criterion are exactly the nest classes
{S, SS, S(SS), …, S(S(S(S(SS))))} — precisely the gadgets whose runs terminate without inspection (Lemma 5).
**Significance.** Observation H is now a theorem for all gadget sizes: a counter layer `S Y1 Y2 x` placed above a
passenger can never hand its predecessor back as clean data inside one head run. Theorem H(b) also turns any
symbolic gadget specification into a *finite* necessary condition (a polynomial identity on M35), so
non-existence of gadgets for a given encoding template can be proved for all sizes by finite search.

## Theorem H3 (no S-term can hold three data) — PROVED (Theorem H + certified finite facts)
For every closed S-term K and opaque x, y, z, the head run of `K x y z` opens a variable (hands control to x,
y or z) or diverges. Equivalently (λ-calculus reading): every S-term applied to three free variables either has
no weak head normal form or one whose head is one of those variables.
*Proof.* Safe3 = {κ ∈ M35 : κ·ξ·ψ·ζ ≠ ⊥ for all ξ,ψ,ζ} is empty (finite check, E17); apply Theorem H(a). ∎
## Theorem H2 (holding two data) — PROVED
Safe2 = {κ : κ·ξ·ψ ≠ ⊥ ∀ξ,ψ} = the six nest classes {S, SS, S(SS), S(S(SS)), S(S(S(SS))), S(S(S(S(SS))))}.
Hence for every closed K whose M35-class is not a nest class, the head run of `K x y` inspects x or y or diverges.
(For nests themselves the run is the Fibonacci peeling, Lemma 5, which leaves the data in control.)
Also Safe1 has 23 classes (code applied to one datum can often run without inspecting it).
**Reading.** Closed code can never receive three independent data without immediately handing control to one of
them, and can receive two only in the trivial/nest cases. Every S-computation is *data-driven*: control passes
to data at every step. Sanity: 20,000 random K (2–22 leaves): 10,863 runs stuck on x, 2,598 on y, 6,539 diverge,
0 reach an hnf (E17).

## Lemma 8 (data conservation) — PROVED (elementary; gives H1, H2-necessity, H3 without any finite model) and MACHINE-CHECKED (lean/BarrierJ.lean, 2026-10-27)
*Lean:* `dcount_step` (a step never lowers the number of data elements), `no_hnf_of_three_data` (Corollary (i): from >= 3
data elements no list of length <= 2 is reachable; an atom-headed front is stuck). Axioms: propext, Quot.sound.
`cor8ii` (Corollary (ii), 2026-10-27): from a list with at least two data elements, all atom-headed, every data element of
every later list of a run that reaches an hnf is atom-headed (standard axioms).
Fix a set of opaque variables. Call a stack element *data* if it contains one. In any head step
`[a,b,c]++R ⇒ ch(a)++[c, b·c]++R` in which a is not variable-headed, the number of data elements does not
decrease. *Proof.* If a is closed, ch(a) is closed and the change is [b·c data] − [b data] ≥ 0 (c survives
unchanged). If a is data with head S, its variable lies in some argument, so ch(a) contains ≥ 1 data element:
change ≥ 1 − 1 + 0. ∎
**Corollaries.** (i) A run whose list contains ≥ 3 data elements at some point must open a variable-headed
element or diverge (an hnf has ≤ 2 elements). Hence `K x y z` inspects or diverges (Theorem H3, now elementary), and
`S g1 … gj x w` with j ≥ 2 inspects or diverges (Corollary H1 for all j: x can only reach position ≤ 2 through position 3,
since a step moves an element up by at most one place; at that step the two elements above it are closed (data arise only
by combining with x or w), so the step `[p, q, x, …]` creates a third data element `q·x`). [Audit fix: originally argued
only for j = 2, and "always inspects" ignored divergence.]
(ii) (Data-driven continuation) Suppose at some point the list contains exactly two data elements, both
variable-headed (e.g. the initial list `ch(K) ++ [x, w]`). If the run **terminates** and never opens a variable-headed
element, then no step with closed b and data c can occur afterwards (it would create a third data element, which can never
disappear again, while an hnf has ≤ 2 elements), so every new data
element is `b·c` with b data; since only closed elements can be opened, induction shows *every data element stays
variable-headed*. Hence every component of the final hnf that contains x or w is headed by x or w: closed code
never ends up holding data — the data are in control.
**Reading.** Independent data can coexist only nested inside one another ("data holding data", the controlling
datum's code acting on the others). This is the exact structural content behind Prop. G and the failed
two-counter constructions; universality, if true, must come from a data-driven design (tag-system-like), not
from a program with registers.

## Lemma 9 (no writing into data while two data are live) — PROVED (from Lemma 8 and Lemma 7); core MACHINE-CHECKED
*Lean (lean/BarrierJ.lean, 2026-10-27):* `lemma9_nowrite` — in a run that reaches an hnf, once the list holds at least
two data elements, no later step has b closed and c data; part (a) is `cor8ii`. Standard axioms. Part (b)'s reading
(what code can still do: select components and nesting) is not formalised.
Suppose at some point of a head run the list holds exactly two data elements, both variable-headed, and the run
**terminates** without opening a variable-headed element. Then (a) every data element stays variable-headed (Lemma 8(ii));
(b) a closed element can be appended to a data element only if it lies *below* that data element; closed
elements pushed by opening code appear at the top, above every data element, and elements only move down
inside a compound `b·c` placed directly below c, so code-generated closed material can never get below a data
element. Hence every data-containing component of the final hnf consists of data heads applied to material that
was already at or below them at that point: **the program cannot write new symbols into the data**; it can only
select the component and the nesting (which datum absorbs which).
With a *single* data element, code can wrap it (e.g. `N_1·W_r = W_{r+1}` in Theorem C): one unbounded datum
can be pushed onto from the front.
*Audit note (independent audit, see end of file).* Termination is needed: for the divergent run on `[Ω, S, x, w]` with
Ω = S(SSS)S(SSS) (hnf-free by Theorem A), the first step creates the S-headed data element `S x` and the run then stays
inside the reduction of Ω forever, so (a) fails without the hypothesis. Part (b) was re-checked on 493 random terminating
runs (0 violations).
**Reading (precise obstruction to register/tag constructions).** Per Böhm-tree step: either one datum, which code
may extend at the front (pushdown-like), or several data that code may only rearrange (data-holding-data,
with every rotation leaving the duplicate created by c-duplication). Tag-system appends at the end and
register updates are both of the forbidden kind. Universality would need rearrangement-only dynamics to be
universal; the natural formal target for the opposite (H1) is a simulation of Böhm-tree paths by a
pushdown-with-copying (higher-order pushdown) system.

## Lemma 10 (no junk-free rotation) — PROVED and MACHINE-CHECKED (lean/Lemma10.lean, 2026-10-27)
*Lean (`lemma10`, standard axioms):* the invariant J1, J2, K below is preserved by every head step (`inv_step`), for a
start (A ++ X :: B) ++ Y :: C with A, B, C free of both atoms, X free of y and Y free of x. This is slightly more general
than the statement: X and Y need not be variable-headed. An atom-headed front is stuck in the Lean machine, so the run
never opens a variable-headed element.
Let a head run start with two variable-headed data elements x above y (plus closed elements) and never open a
variable-headed element. Then every element headed by y that contains x contains at least two occurrences of y.
*Proof (replaced after the audit: the original used Lemma 8(ii), which needs termination; this one does not).*
Invariant J: (J1) no list element containing y lies above an element that contains x but not y; (J2) inside every
S-headed subterm of every element, no spine argument containing y precedes a spine argument that contains x but not y.
Initially J holds (x above y; the only elements with variables are x and y). Consider a step
`[a,b,c]++R ⇒ ch(a)++[c, b·c]++R` with a S-headed. Among ch(a) J1 holds by J2 for a; an a_i containing y above some E
containing x but not y (E = c, b·c or in R) would mean a — which contains a_i — was above c, b or E, violating J1 before.
The clean c above b·c is harmless (b·c contains c); c or b·c above E in R inherits an old pair. For the new S-headed
compound b·c (spine = spine(b) ++ [c]): a spine argument of b containing y before c containing x but not y would mean b
(above c) violated J1. So J is preserved. Now every y-headed subterm containing x contains y twice: new subterms are only
b·c; if b·c is y-headed and contains x then either c contains x but not y (excluded by J1, b being above c), or c contains
y (two y's), or x lies in b, which then is a y-headed subterm containing x (induction). ∎
(Audit check: 25,000 random runs, 19,343 with S-headed data: 0 violations of the lemma or of J.)
**Consequence.** With two live blocks, the bottom block can be brought in front of the other only together with a
second copy of itself; order-preserving combinations (`x y`) are duplicate-free inside their component (the clean
copy of y goes to the other component). Together with Lemma 9: Böhm-tree steps can prepend to a single datum,
preserve the order of several data, or rotate with duplication — never write into data or rotate cleanly.

---------------------------------------------------------------------------------------------------
## H2-loophole hunt (bounded attempts, 2026-10-25) — results
### Theorem J (global writes) — PROVED and MACHINE-CHECKED (lean/BarrierJ.lean, 2026-10-27: `theoremJ` (ii), `theoremJ_unique` (iii), `theoremJ_global` (i): at a write every other element is atom-free; standard axioms)
In a terminating head run that never opens a variable-headed element, call a step a *write* if b is variable-free
and c contains a variable. Then (i) every write's c contains every variable present in the run; (ii) the data
count is 1 immediately before a write and 2 after; (iii) there is at most one write per run.
*Proof.* A write leaves c and creates the new data element b·c, so it raises the data count by one; by Lemma 8 the
count never decreases, and a head normal form has ≤ 2 elements. If c missed some variable v, the element holding
v would be a third data element after the step. ∎ (Random check: 5,065 terminating runs, 0 violations.)
**Reading.** Writes that do not inspect the unknown parts are *global*: at most one closed layer per Böhm-tree
step, wrapped around all unread data at once. Runs that leave part of the configuration unread therefore realise
only prefix rewriting (read a prefix, prepend one closed compound) — pushdown power.
### Lemma L (two components) — PROVED
Every head step leaves ≥ 2 list elements; hence any term needing at least one head step has an hnf with exactly two
components. Zero/one-component hnfs are exactly `S` and `S x` themselves.
**Corollary (no persistent control).** In the pair automaton `(p,q) + a ↦ App(H(p a), q a)` the accumulator is left
untouched (`q·a`) only if `H(p a)` has one component, which by Lemma L forces p = S and makes the next control the
absorbed symbol a. A control reproducing itself exactly (`p a →* S p`) is impossible for |a| > 1 by leaf count.
### Proposition M (no first-to-end transfer in one uniform pass) — PROVED under stated assumptions
Assume (U-tail) unread symbols are opaque until read and (U-acc) the accumulated output is not reopened within the
pass. While an unread symbol remains, the accumulator and that symbol are two data elements, so by Theorem J no
symbol's code can write into either; by the Corollary the control cannot persist. Hence information about the
first symbol can enter the output only at its front (Lemma 9) — never after the last copied symbol — so a single
uniform pass cannot perform a tag-system append. (Exact search, gadgets ≤ 4 leaves, words ≤ 6: 0 of 5,832.)
### Attempts and status
| attempt | outcome |
|---|---|
| parity / modular counting along wrapper countdowns | none (729 combos); structurally impossible: countdown nodes are `V_m Y` with fixed Y (memoryless) |
| single-datum FRACTRAN arithmetic | multiplication via iteration exists; division needs modular tests — blocked by memoryless countdowns and global writes |
| CPS / data-driven two counters | blocked: Theorem J (writes global), write-freeze for separated data, Lemma 10 |
| tag-system pass with end marker | blocked under U-tail/U-acc (Prop. M); search negative |
| **open loophole** | information carried by output *shape* (nesting chosen by read symbols), propagated ≤ 1 position per pass (CA-like), with duplicates as by-products; and non-head reduction strategies (local writes inside subterms) |

## Theorem N (bounded growth of separated counters) — PROVED (non-appending layers); appending case OPEN
Let x, y be opaque. For a term T define LD_x(T) = the maximum, over occurrences of x in T, of the number of nodes
u·v on the root-to-occurrence path such that u is variable-free, v contains the occurrence, and u·v contains no y.
Consider a Böhm-tree path N_0, N_1, … in which every step is a head run that never opens a variable-headed element
and every N_i is S-headed with at least two list elements containing variables ("separated"). Then
**LD_x(N_i) ≤ LD_x(N_0) for all i** (and symmetrically for y).
*Proof.* Separated ⇒ each run starts with ≥ 2 data elements ⇒ no write (Theorem J). Every element created by a
step is a subterm of an existing element (ch(a), c) or a compound b·c. For occurrences of x inside b the new root
node is not counted (x is in the left child); for occurrences inside c it is counted only if b is variable-free and
b·c contains no y — i.e. only for a write, impossible. Hence every element's LD is ≤ the maximum over the run's initial
list elements, which is ≤ LD of the node (the spine nodes only add counted nodes). The next node is a final element. ∎
(Random check: 7,348 terminating runs with x, y separated: 0 LD increases; separation persisted in all.)
**Corollary N1 (no uniform two-counter growth).** Encode counters as ⟨n⟩_i = L_i^n[Z_i] with *non-appending* layers
(the hole is not at the head of L_i[·]; then each layer adds ≥ 1 to LD) inside configurations C_q[⟨a⟩_1, ⟨b⟩_2] with the
two holes in different list elements, and simulate each instruction by Böhm-tree steps that never open a counter
below the layers it explicitly reads. Along any computation segment in which counter 2 is never read below some
depth (its deeper part y stays opaque) and counter 1's deep part x stays opaque, counter 1 can rise by at most
LD_x(N_0) (and symmetrically). Consequently neither `loop: INC1; INC2` nor the transfer loop
`while c1>0: c1--, c2++` (take the first m < a iterations, x = ⟨a−m⟩) can be simulated for all inputs; hence no
universal two-counter machine (Minsky's constructions rely on transfers) has such a simulation.
**Scope (do not over-read).** Proved only for: uniform (non-inspecting) steps, separated encodings, non-appending
layers, head-reduction/Böhm-tree semantics. Open: appending layers `u ↦ u c₁…c_r` (the naive "submerged closed
leaves" potential fails: duplication copies closed leaves inside data, counterexample K = SS, middle SS);
entangled encodings (counters nested in one block — then all writes are global, Theorem J); non-uniform steps that
read counters arbitrarily deep; non-head reduction strategies (local writes inside subterms are possible there).


## Theorem N* (potential bound for counters, ALL layer shapes) — PROVED (supersedes the scope of Theorem N)
For an occurrence-wise path in a term, define (x, y opaque):
 LD_x  = max over occurrences of x of #{nodes u·v on the root-to-x path : u variable-free, x ∈ v, y ∉ u·v};
 SUPP_x = max over occurrences of x of #{nodes u·v on the root-to-x path : x ∈ u, v variable-free}.
**Claim.** For an occurrence o of x let P(o) = LD(o) + SUPP(o) (the two counts along o's own path) and
P_x = POT_x = max_o P(o). Along any Böhm-tree path whose head runs never open a variable-headed element, if every node
contains y, then P_x never increases. (The same case analysis shows that max LD and max SUPP are each non-increasing,
so the original "max LD + max SUPP" wording was also correct — the per-occurrence restatement is harmless but was not
needed; independent audit: 0 violations in exhaustive single steps to 9 leaves and 35,387 random steps.)
*Proof.* Work with lists: for a list [e1,…,em] count, for an occurrence of x in e_i, its count inside e_i plus the number
of variable-free e_j with j > i (these are exactly the spine nodes of S e1…em counted by SUPP). Check one step
`[a,b,c]++R ⇒ ch(a)++[c, b·c]++R`: occurrences in R, in the clean c, inside b·c via c, inside b·c via b
(append: +1 inside, −1 from the closed c no longer below), and in ch(a) (a S-headed: spine count of a becomes
closed elements below) do not increase (the ch(a) case can lose [b closed] − [b·c closed] and a junction LD-node);
LD only changes at new nodes b·c, and a new LD-node needs b
variable-free and x ∈ c with y ∉ c — a write whose c misses y, impossible by Theorem J since y is in the run.
A final element taken as the next node has count ≤ its count in the final list, and the list count of a node's spine
arguments is at most its term count (the term count may include one extra "junction" LD-node (S e1…e_{i−1})·e_i), so
the inequalities chain in the right direction. ∎
(Random check: 5,541 components containing x and y: 0 increases of SUPP, LD or LD+SUPP.)
**Layer lemma.** For any closed one-hole context L ≠ [·], every node on the path from the root of L[u] to u is either
(hole in the right child, closed left) — an LD-node, provided the hole content u does not contain the other variable —
or (hole in the left child, closed right) — a SUPP-node; so each layer adds ≥ 1 to POT_u when u is free of the other
variable (with the other variable inside u, e.g. L[u] = S u adds 0).
**Corollary N*.** Let counters be encoded *unentangled*: ⟨a⟩_1 = L_1^a[Z_1], ⟨b⟩_2 = L_2^b[Z_2] (any closed layers,
appending or not), plugged into separate holes of state contexts C_q. Simulate each instruction by Böhm-tree steps
that never open a counter below the layers they explicitly read. Then along any segment that leaves the cores x, y
unopened, counter 1 can never carry more layers above x than POT_x(N_0) (similarly counter 2). Hence neither
`loop: INC1; INC2` nor the transfer loop `while c1>0: c1--, c2++` (first m < a iterations, x = ⟨a−m⟩, y = ⟨b⟩) has
such a simulation for all inputs; no universal two-counter machine is simulable in this way.
**Scope.** Head-reduction/Böhm-tree semantics; uniformity (non-inspection of cores); unentangled encodings.
Still open: entangled encodings (both counters inside one block — writes are then global, Theorem J), steps
that read counters arbitrarily deep (cascades), and non-head reduction strategies.

---------------------------------------------------------------------------------------------------
## Lemma 11 (full-read principle) — PROVED (+ exact random check)
*Reading.* The head run of t = S e1 … em builds every element from residuals of subterm occurrences of t (spines are
split, c is shared, b·c is new; Lemma 2). An occurrence u is **read** if some opened element has a residual of u on its
left spine — or, across Böhm-tree steps, lies on the left spine of a node whose spine is split into the next run's list
(audit fix: this split reads without any opening); e_i is **fully read** if every occurrence in e_i is read.
**Claim.** If the **closed** term t has a head normal form, then (i) of any three disjoint occurrences lying in three different arguments,
at least one is read; hence (ii) at most two of e1, …, em are not fully read; (iii) the same holds for the list at every
point τ of the run (apply (ii) to the term S L_τ, whose head run is the rest of the run).
*Proof.* Replace u1, u2, u3 by fresh variables. The variable run equals the original modulo the replacement until it
opens an element with some x_j on its left spine, which happens exactly when the original reads u_j (all residuals of u_j
are shared copies, all replaced). If none is read, the variable run never opens a variable-headed element and terminates
with the original, although it starts with ≥ 3 data elements — contradicting Lemma 8 (an hnf has ≤ 2 elements). ∎
**Cost corollary.** A step opens one element and marks exactly one leaf (its head), so a terminating run costs at least
Σ_{e_i fully read} |e_i| (leaves). Hence a Böhm-tree node with ≥ 3 unbounded spine arguments has an unbounded-cost step,
and after an element with a long spine is opened (e.g. an appending counter `Z c⃗ … c⃗`, a·r closed arguments pushed),
the rest of that run costs ≥ a·r − 2.
(Closedness is needed: for symbolic t = S x e2 e3 e4 the hnf x e3 (e2 e3) e4 leaves three arguments unread — audit.)
(Exact check, code/fullread.py: 2,729 random terminating runs, m = 3..7 arguments of ≤ 9 leaves: number of not fully
read arguments {0: 7, 1: 141, 2: 2,581}; 0 violations.)

## Lemma 12 (right-depth cost) — PROVED
The right-depth of an occurrence in an element is the number of right edges from the element's root to it. Let D_τ be
the least right-depth of a residual of u among the elements at time τ. A head step lowers D by at most 1 (only the
opened element's spine arguments lose one right edge; c keeps its depths, b·c adds one to c's), and u is read at a step
opening a residual at right-depth 0. Passing from a component p to the spine arguments of the next node lowers right-depth
by at most 1. Hence **reading an occurrence at right-depth r costs ≥ r (head steps + Böhm-tree steps)**. ∎
For a counter ⟨n⟩ = L^n[Z] with a *non-appending* layer (hole not on the left spine of L) the core below d layers has
right-depth ≥ d; for an *appending* layer (`L[u] = u c1 … cr`) every core is on the counter's left spine, so the first
read of any part of the counter opens all of it (cost ≥ n·r − 2 by Lemma 11).

## Theorem O (growth beside an unread counter is expensive; bounded-cost 2CM simulations are impossible) — PROVED
*Setting (all assumptions explicit).* (E1) unentangled unary counters ⟨n⟩_i = L_i^n[Z_i], L_i closed one-hole contexts
≠ [·] (any shape), Z_i closed; ℓ_i = |L_i|, z_i = |Z_i| (leaves), h_i = depth of the hole of L_i. (E2) checkpoint nodes
are *exactly* C_q[⟨a⟩_1, ⟨b⟩_2] for finitely many closed two-hole contexts C_q (incomparable holes); H = max hole depth.
(E3) Böhm-tree semantics: the simulation follows one Böhm-tree path, visiting the checkpoints of the simulated counter
program in order; an instruction that changes a counter moves to a different checkpoint node, so it costs ≥ 1 (hence
|α|, |β| ≤ c below — an assumption made explicit after the audit). The **cost** c of a stretch = its number of head
steps plus Böhm-tree steps. K_0, κ below are constants
depending only on the C_q, L_i, Z_i (κ = max(1, ℓ_1/ℓ_2)).
**Claim.** Let a stretch of cost c go from C_q[⟨a⟩_1,⟨b⟩_2] to C_{q'}[⟨a+α⟩_1,⟨b+β⟩_2], |α|,|β| ≤ c, with β·h_2 > H and
b ≥ 2κ(a + c) + K_0. Then a ≤ 2c + K_0, or the stretch reads counter 1 down to depth ≥ a − K_0, or counter 2 down to depth
≥ (b−β)/2 − K_0; in particular **c ≥ a/2 − K_0** (Lemma 12; for an appending counter any read costs ≥ n·r − 2;
β ≤ c; under the hypothesis min(a/2, b/3) = a/2). Symmetrically for counter 1.
*Proof.* Let D_i be the depth to which counter i is read — "read" as in Lemma 11, including occurrences on the left
spine of a Böhm-tree node of the stretch (audit fix: a core residual heading a node would make the variable version
variable-headed without any opening) — and put x := core of counter 1 at depth d_1 = D_1+1, y := core of
counter 2 at depth d_2 = D_2+1. Suppose a > 2c + K_0, a − d_1 ≥ K_0 and b − d_2 > d_2 + β + K_0 (else we are done); the last gives
|Y| ≥ (b/2)ℓ_2 > |⟨a+α⟩_1|. Neither core is
read, so the variable version N_0^var = C_q[L_1^{d_1}[x], L_2^{d_2}[y]] follows the stretch symbolically to N^var with
N^var[X,Y] = C_{q'}[⟨a+α⟩,⟨b+β⟩] =: N, X = L_1^{a−d_1}[Z_1], Y = L_2^{b−d_2}[Z_2], both larger than every ℓ_i, z_i.
Let R = ⟨b+β⟩_2 be the subterm of N at hole 2 and walk down R's *hole path* (the chain of its b+β layers to Z_2).
(1) R is not inside a substituted X or Y (|R| > |X| as b ≥ 2κ(a+c); |R| > |Y| as β > −d_2). So hole 2 is a position of
N^var with subterm T, T[X,Y] = R. (2) A head step creates exactly one new node (b·c) and Böhm-tree steps none, so at most c
nodes of N^var are new; every other node is a residual of a node of N_0^var and carries an unchanged copy of its
subtree. Let ρ be the first residual node on T's hole path: above it ≤ c new nodes, i.e. ≤ c/h_2 + 1 layers. If ρ's
subtree s is closed, it is a closed subterm of N_0^var (from C_q, side parts of layers, Z's), so R has ≤ c/h_2 + 1 + J_0
layers (J_0 a constant) — contradicting b ≥ c + K_0. If s contains x but not y, the tail of R inside the copy of s is
s[X] = L_2^{j'}[Z_2] with j'·ℓ_2 ≤ |s| + |X| ≤ |C_q| + d_1ℓ_1 + (a−d_1)ℓ_1 + z_1 (s lies on x's path in N_0^var; leaf
count, valid for any layer shapes), so b+β ≤ c/h_2 + 1 + κa + O(1) — contradicting b ≥ κa + c + K_0. If s contains both
x and y, then s[X,Y] contains copies of X and Y at incomparable positions; both are larger than every side part of L_2 and
of Z_2, but only one position can lie on R's hole path — impossible (audit: this case was missing). Hence s contains y
but not x, the copy of Y lies on the hole path (a copy of Y in a side part of a layer is impossible by size), x does not
occur in T (a copy of X would have to sit in a side part — too big), y occurs once in T, and T = D[y] with
D[Y] = L_2^{d_2+β}[Y]; as |Y| exceeds both contexts, D = L_2^{d_2+β} (otherwise Y would be a proper subterm of itself or of
a closed side part).
(2′) N^var contains x: apply the walk of (2) to counter 1's region R_1 = ⟨a+α⟩_1. It is not inside a copy of Y: such a
copy would be the subterm of N at a node of C_{q'} at or above hole 1, i.e. R_1 itself (but |Y| > |R_1|), or C'[R_1] for a
part C' of C_{q'} (|C'[R_1]| ≤ |C_q| + |R_1| < |Y| once K_0 > |C_q| + z_1), or a subterm containing R (larger than |Y|)
(audit fix: "|Y| > |R_1|" alone points the wrong way — a smaller term can sit inside a larger one); new nodes plus a closed residual give ≤ c/h_1 + 1 + J_0 < a + α layers (a > 2c + K_0, α ≥ −c); a residual
containing y would put a copy of Y inside R_1 — too big. So the first residual on R_1's hole path contains x.
(3) Every node on the hole path of each layer of T is an LD- or SUPP-node for y (closed sibling, no x), so
P_y(N^var) ≥ (d_2+β)h_2, while y occurs once in N_0^var, so P_y(N_0^var) ≤ H + d_2h_2. Every node of the stretch contains
x (N^var does by (2′), and Böhm-tree descendants are built from subterms). Theorem N* (per-occurrence form) gives
P_y(N^var) ≤ P_y(N_0^var), i.e. βh_2 ≤ H — contradiction. ∎
**Corollary O1 (bounded cost ⇒ no two-counter simulation).** If every simulated instruction costs ≤ K, take m > H/h_2
iterations of `L: INC2; goto L` or of the transfer loop `while c1>0: c1--, c2++` from inputs a > 2mK + 2K_0,
b ≥ 2κ(a + mK) + 3mK + 3K_0: the stretch costs ≤ mK < a/2 − K_0 and gains m > H/h_2 — impossible. So neither loop has a
bounded-cost simulation under (E1)–(E3). Machines whose runs contain arbitrarily long transfers (as Minsky's universal
two-counter machines do) are excluded too, by a window argument (audit correction of the earlier parenthesis): in a
transfer of A units into a target starting at b_0, after k units the counters are (A − k, b_0 + k); for A large some
k ≈ (2κ/(2κ+1))·A gives A − k > 2mK + 2K_0 and b_0 + k ≥ 2κ(A − k + mK) + 3mK + 3K_0, and the next m iterations then
contradict the claim. This removes the uniformity hypothesis of Corollary N*.
**Corollary O2 (transfers cost Ω(a²)).** For b ≥ 4κa + K_0 (b only grows), every block of m > H/h_2 transfer iterations
costs ≥ a_current/2 − K_0 (if b ≥ 2κ(a + c) + K_0 fails then c > a anyway), so a stepwise transfer from (a, b) costs
≥ a²/(4m) − O(a). Growing one counter beside a large unread
counter requires (nearly) fully re-reading one of them — the only designs not excluded are full re-execution designs.
**Remarks.** (i) H enters only through the *first* checkpoint of the stretch: potential stored in garbage above a counter
can be spent, but never replenished while the other counter is unread (P_y is globally non-increasing). (ii) Nested
entangled encodings `L_1^a[M[L_2^b[Z]]]` (unique parsing) freeze the inner counter for stretches of cost below about
a/2, by the parsing half of the argument alone (with one core no potential argument is available — audit correction of
the earlier "cost < a"). **Scope (do not over-read).** Proved only under (E1)–(E3) with exact checkpoints. NOT covered: genuinely
entangled encodings (e.g. Gödel numbering in one counter — full-read regime), checkpoints with unbounded garbage
contexts, full re-execution designs, and non-head reduction strategies.

---------------------------------------------------------------------------------------------------
## Master Reduction — what exactly a complete disproof needs (2026-10-27, main agent)
This collects Theorem T, Propositions CF, R, P and UB into one statement, so that every result has a fixed place.
*Setting.* A putative universal emulation of a machine U with undecidable halting problem consists of a computable
encoder w ↦ t_w, an evaluation order Ord (any fixed strategy, or the multiway system), and a halting detector that is
not itself universal. Detector classes:
* (D1) halting = "the evolution stops" or "the multiway graph is finite";
* (D2) halting = an MSO-definable property of the Böhm tree BT(t_w);
* (D2′) halting along a Böhm-tree path ρ, for emulations that are modular at halting (Proposition R);
* (D3) halting = the first step whose bounded (k, d)-window is accepted by a finite automaton (leftmost-outermost);
* (D4) halting = the first step whose WHOLE state, serialised head first, is accepted by a finite automaton;
* (D5) any other detector.

*Lemma W (whole-state automata) — PROVED (Carton–Thomas, as in Proposition UB).* Let σ be a morphism from the free
monoid on the serialisation alphabet into a finite monoid. If, for every σ, the infinite word (σ(config_n))_{n ≥ 0}
over that finite monoid is effectively profinitely ultimately periodic (call this *configuration-level R″_PUP*), then
"some config_n is accepted by a given automaton A" is decidable: take σ the transition morphism of A. Then the
property is MSO over that word, and decidable by Carton–Thomas. ∎ Configuration-level R″_PUP implies window-level
R″_PUP, because a window is a bounded-cost function of the serialisation.
*Master Reduction — PROVED given the hypotheses below.* No emulation of U exists whose detector is of class:
* (D1) unconditionally (Theorem T);
* (D2) for every order and for multiway, given C5′ (MSO theory of Böhm trees decidable uniformly in t). Böhm-tree
  properties are order-independent (Theorem T (2), Proposition CF);
* (D2′) for path ρ, given decidability of "the ρ-path is infinite" (Corollary R1). The models L36, R19 and LO204
  are conjectured to decide it; one half of each is proved (Proposition Q″);
* (D3) for leftmost-outermost, given effective window-level R″_PUP (Proposition UB);
* (D4) for order Ord, given effective configuration-level R″_PUP for the Ord-evolution (Lemma W).

Class (D5) — detectors that do more than read a finite-automaton property, e.g. compare sizes of distant subterms — is
NOT covered. A disproof must argue that Wolfram's "not itself capable of universal computation" excludes them, or treat
them separately. This is the definitional piece.

*Hypothesis ledger (2026-10-27).*

| hypothesis | status |
|---|---|
| C5′ (MSO of Böhm trees decidable) | open; special cases: Q10 PROVED and MACHINE-CHECKED in Lean (hnf), C6 soundness half PROVED, C8 one half PROVED, path models one half PROVED (Q″); completeness halves certified ≤ 19 / ≤ 16 leaves; the leftmost-half size-change route fails with finite abstractions (FAILED_APPROACHES 29) |
| window/configuration R″_PUP, leftmost-outermost | open in general. PROVED per term for every certified run: all 152 census counters, 850/850 random endpoints, the loop/nest/call/comb certificates; R″_PUP PROVED for nested loops (Lemma PUP) and the head-unique class (Theorem UR-C, Lean). Attack in progress: the non-universality agent's phase programme (OT, OTD, FH, SL, canonical_innermost in Lean) toward "re-execution is call-like" |
| configuration R″_PUP, parallel and other orders | open; 86/150 parallel runs certified per term (Theorem LP-par) |
| (D5) definitional argument | open (not a mathematical statement until a detector class is fixed) |

So a complete disproof = C5′ + configuration-level R″_PUP for every order the emulation may choose + the (D5) argument.
A universality proof must break one of these: a construction is impossible in (D1), and in (D2)–(D4) it would refute the
corresponding hypothesis.

## Construction-agent obstruction theorems (2026-10-26/27; machine-checked parts re-verified by the main agent)
A background construction agent (started at the user's request) tried to engineer data-dependent control. It found no
construction. Its obstruction results:
* *Theorem OT and Lemma RC — PROVED, MACHINE-CHECKED* (lean/AgentOT.lean, a copy of agent_work/lean/OT.lean; 632 lines;
  axioms propext, Classical.choice, Quot.sound; no sorry; re-compiled by the main agent, and the definitions of step,
  ppy, ordered and badPairL were checked against the statements below). Setting: the generic run from
  args G ++ [y, x·y, r] with opaque atoms b, x, y, r; an atom-headed front is stuck.
  * `rc_main` (Lemma RC): for closed G, every subterm of every reachable element that contains y exactly once and
    neither x nor r is y itself or a right comb d1·(d2·(…(dm·y))) with every d_i closed. So the only clean
    single-occurrence values code can write from its input are left multiplications by closed terms.
  * `ot_main` / `ot_no_transfer` (Theorem OT): if G is *ordered* (in every S-headed subterm the closed spine
    arguments come first) and contains no y, then no b-containing element ever sits above a proper right comb
    d1·(…(dm·y)), m ≥ 1. In particular the run never reaches [b-front, w, v, …] with w or v such a transformed
    handler. Right combs are ordered, so a datum written by code can never drive a proper Church-style transfer.
    This explains, at all sizes, Theorem U's "straight-line only".
  * Scope: generic opaque data, one occurrence of the datum, closed wrappers, clean hand-offs only. NOT covered:
    dirty wrappers that contain the old predecessor, writes that duplicate a datum (as in the binary counter's
    levels), and full re-execution designs. Its invariants I1/I2 are this file's F1/F2; the "bad pair" invariant is new.
* *Lemma OC (occurrence counting), Corollary OC1 and `no_transparent` — PROVED, MACHINE-CHECKED* (lean/AgentOC.lean;
  axioms propext and Quot.sound only):
  * a head step raises the occurrence count of an atom v by exactly its count in the third element;
  * every closed T ≠ S activated generically leaves at least 3 copies of v at any stuck list;
  * hence S is the only closed term with rule [v·w, (u·v)·w′, closed…], so agent U's pump [S, T, S] → [S, T·S]
    cannot get a second alphabet letter.
* *Lemma NC (numeral chains) — PROVED by hand by the agent* (agent_work/LOG.md; not independently audited). Along a
  numeral chain the handler always receives the same second input, so a numeral loop cannot carry changing state in
  its inputs.
* *Comb parity — PROVED (elementary).* A left comb S^n·S is a Church numeral for (u, v) ↦ (v, u·v), and [S^n S, J, K]
  gets stuck at K for even n and at J for odd n. Comb parity is testable; numeral parity is not.
* *Bounded searches — COMPUTATIONALLY CERTIFIED within the stated bounds* (agent_work/*.py; LOG.md):
  * numeral parity in 1-hole contexts ≤ 10 leaves (n ≤ 8): none;
  * numeral parity in [N_n, x, y, J, K, L] with x, y ≤ 7 leaves (38,809 pairs, n ≤ 10): none, outcomes change at
    most once;
  * comparison of two numerals in all 2-hole contexts ≤ 9 leaves (134,142): none;
  * two-way Church transfer pairs ≤ 11 leaves: none;
  * transfer graph ≤ 10 leaves (2,559 edges): every target is a right comb, no proper→proper chain;
  * loop bodies ≤ 7 that transform a state slot: none;
  * dirty transfer chains ≤ 9 leaves: at most 2 proper phases.
  * Random check of Theorem OT: 12,691 ordered runs gave 0 violations; unordered contexts gave 2,434 bad pairs in
    21,929 runs, so the test does detect them.

*Phase 3 (2026-10-27): dirty wrappers.* Setting: the generic phase model. A datum has one live predecessor atom p and
frozen atoms c_i (earlier predecessors), and a frozen-headed front is stuck. A phase ends in one of four ways:
TRANSFER (a p-headed front), CALL (an x-, y- or r-headed front), REEXEC (a c-headed front) or DIVERGE.
* *Theorem OTD — MACHINE-CHECKED* (lean/AgentOTD.lean). This is Theorem OT with frozen atoms allowed ("closed" = free
  of p, x, y, r). An ordered datum makes no proper transfer whose wrappers are all p-free, so every proper transfer
  from phase 2 on is dirty.
* *Lemma FH — MACHINE-CHECKED* (`fh_main`, `fh_rcomb`; axiom propext only). If some level of d1·(…(dk·p)) has a
  frozen-headed wrapper, no p-headed element ever appears. That phase makes no transfer before it re-executes the
  frozen value.
* *Theorem SL — MACHINE-CHECKED* (lean/AgentSL.lean, 790 lines; `sl_main`, `sl_step_lemma`). For a single-level datum
  K·p, every element that contains p and no x, y, r and is glued onto an x/y/r-element is p-headed.
* *`canonical_innermost` — MACHINE-CHECKED* (lean/AgentCANON.lean, 1,288 lines). For K·p, whenever the run reaches
  f :: w :: d1·(…(dm·y)) :: rest with f containing p, the innermost wrapper dm is p-headed. Stated for position 3;
  position 2 is analogous but not formalised.
* *Corollary* (proved; machine-checked except the renaming p ↦ frozen c, which is not formalised). A transferring
  phase with single-level data cannot iterate without re-executing a frozen value. The canonical Church chain makes
  at most two transfer phases before re-execution.
* *Multi-level data — COMPUTATIONALLY CERTIFIED only.* Phase 3 is never a proper transfer:
  * right combs ≤ 11 leaves: 23,713 data;
  * ordered contexts ≤ 10 leaves: 16,795 data, with 1,155 proper phase-2 transfers;
  * random data with wrappers ≤ 25 leaves: 70,000.

  Negative control: phase-3-shaped data with random closed parts CAN transfer. So a proof needs the "replay" relation:
  dirty wrappers are copies of the datum's own levels, whose code re-runs on the frozen remnant.
* *Duplicating writes (partial).* OT, OTD and FH never assume the datum occurs once, and binary-counter levels are
  ordered, so these theorems apply to them; SL and `canonical_innermost` need single-level data. Lemma RC2 (hand proof,
  not in Lean): written values with any number of y's have all maximal closed subterms in function position.
* *The remaining regime (definition, agent_work/LOG.md "Task 3").* A run is in the re-execution regime if every cover
  of it by generic phases has infinitely many REEXEC phases. Runs outside it eventually have only CALL and identity
  transfers, i.e. data-blind iteration. CONJECTURAL final target: re-execution of a frozen value is call-like (finitely
  many parametric rule schemes per run, as in Theorem CA and Lemma NC), which would give R″_PUP.
* Comb-parity re-execution rounds (`comb_rounds.py`, gadgets ≤ 5 leaves): no non-affine or parity-dependent map found.
* Scope: the generic model only (opaque data, frozen-headed front = stuck), Church-style clean or dirty transfer
  phases only, under the stated data hypotheses. It does not cover full re-execution runs or other evaluation orders.

*Reading.* None of this proves non-universality. It narrows the constructive loophole further: transfers from
code-written data are impossible (Theorem OT); from phase 2 on, transfers are dirty (OTD); and single-level data
force re-execution after at most two transfer phases. A universal design would need multi-level replay, duplicated
data or full re-execution. The agent's suggested next steps: extend Theorem OT to dirty wrappers and to duplicating writes
(leaving full re-execution as the single open case), or design re-execution rounds that use comb parity as the
data-dependent branch.

## The full re-execution frontier (2026-10-25) — what Theorem O leaves, stated precisely
**Canonical surviving design = Theorem C's round** (`K W_r → … → W_r W_{r+1} → W_{r-1} W_{r+1} → … → K W_{r+1}`):
at a *single-datum* moment one global write is made (`N_1 Y = W_{r+2}`, Theorem J), the datum is duplicated, and one
copy is counted down to its base (a full read, cost ≈ r) while the other copy is passive. This matches Theorem O exactly:
the passive copy grows only after the other copy is fully read. Every design that survives Theorems J, N*, O has this
shape: (a) writes happen only when one unbounded datum is live, and wrap all of it; (b) between writes, every other
unbounded structure is fully executed (Lemma 11, Theorem O); (c) the executed material is closed and may act as a
program on the datum (`b·z` with b closed and arbitrarily large). Hence *all unbounded computation happens inside full
executions of closed terms* — global, cellular-automaton-like rewriting — and this regime is not constrained by any result
here. (Small-gadget evidence only: E14 word dynamics, E18, E19 — junk always enters, no deletion, no doubling.)

## Conjecture C5 (H1 master conjecture) — CONJECTURAL
For every closed S-term t, the Böhm tree BT(t) (⊥ for nodes without hnf) is generated by a higher-order recursion scheme
computable from t (equivalently, by a collapsible higher-order pushdown automaton). Evidence: data conservation (Lemma 8),
global writes (Theorem J), no growth beside unread data (N*, Theorem O), copy-and-count-down rounds (Theorem C, Zachos
term, both order-2 phenomena); no counter-example among all exact families tested (E9–E20).
Weaker target **C5′:** the MSO theory of BT(t) is decidable uniformly in t (would settle BEKW Question 5 — productivity —
and Böhm-tree finiteness).
**Proposition P (conditional reduction) — PROVED given C5′.** Suppose a universal Turing machine U were emulated by S-terms
in the following sense: a computable map w ↦ t_w and a fixed MSO formula φ over binary trees labelled {S, ⊥} such that U
halts on w iff BT(t_w) ⊨ φ. Then C5′ makes halting of U decidable — impossible. So under C5′ no emulation whose halting
signal is an MSO-definable (in particular any finite-automaton-recognisable, any "some node has property X", any
finiteness or productivity) property of Böhm trees exists. *Proof.* Decide BT(t_w) ⊨ φ by C5′. ∎
**Scope.** Proposition P concerns Böhm-tree (equivalently leftmost-outermost-limit) semantics and MSO-definable halting
signals. Wolfram's informal criteria also allow decoders reading individual terms of a particular evaluation order;
those are covered only insofar as the decoder's verdicts are MSO-definable on the Böhm tree.

---------------------------------------------------------------------------------------------------
## Conjecture C6 (answer to BEKW Question 5: productivity is regular) — finite facts COMPUTATIONALLY CERTIFIED,
## the conjecture EXPERIMENTALLY SUPPORTED (exhaustive to 19 leaves)
Let P39 be the 39-element magma of data/model39_productivity.txt (generator s = class of S, F_P = 38 classes, ⊥_P one
class). **C6:** a closed S-term t is productive (its Böhm tree has no ⊥) iff [t]_{P39} ∈ F_P.
*Certified finite facts.* (i) s x y z = x z (y z) for all x, y, z (P39 is an S-model, so [·] is a conversion invariant —
Lemma 3); (ii) ⊥_P is two-sided absorbing; (iii) s x y ∈ F_P ⟺ x, y ∈ F_P and s x ∈ F_P ⟺ x ∈ F_P; (iv) the context
monoid is aperiodic (f⁶ = f⁷).
*Evidence.* Exact agreement with the productivity oracle on all ≈ 655M terms with ≤ 19 leaves (E22).
*Consequences if C6 holds.* Productivity is a regular tree language, decidable in linear time, and counter-free (by (iv),
as in Theorem E): BEKW Question 5 answered positively ("regular? decidable?" — yes, yes). By Proposition P's argument, no
emulation can use "the evolution becomes unproductive" as its halting signal.
*What a proof needs (precise).* (a) Soundness of F_P: every term with [t] ∈ F_P has a head normal form; then by (iii) and
conversion invariance its hnf components are again in F_P, and coinduction gives a ⊥-free Böhm tree. (a) is a
Question-10-type statement for P39 (reduced to Q10 itself by Proposition Q via the generated joint magma P39 × M35, although the two congruences are
incomparable). (b) Completeness:
if [t] = ⊥_P then by (iii) every head normal form of t has a ⊥_P component, giving a path of ⊥_P nodes; one must show such
a path cannot be infinite with every node head-normalising (a well-foundedness lemma — the hard direction).
**Proved now (unconditional, from (i)+(iii)):** every normalising term has its class in F_P (normal forms are built by
S, s x, s x y from F_P classes); equivalently [t] = ⊥_P ⇒ t has no normal form.
**Proposition Q (soundness half of C6 reduces to BEKW Question 10) — PROVED** (from a COMPUTATIONALLY CERTIFIED fact) **and MACHINE-CHECKED in Lean 4 (lean/PropQ.lean, 2026-10-27):** `propQ (t) (h : isFP (clsP t) = true) : Productive t`, Productive t := ∀ d, every Böhm-tree node down to depth d has a head normal form; built on the machine-checked Q10; P39's S-identity, its closure facts and the 113-element joint sub-magma with M35 are kernel-checked (no axioms).
*Fact (code/jointmodel.py):* the sub-magma of P39 × M35 generated by (s_P, s_M) — i.e. the joint classes of all closed
S-terms — has 113 elements, satisfies the S-identity, and contains **no pair (productive, ⊥_M)**.
*Claim (now unconditional: its hypothesis is Theorem Q10).* If every term with [t]_M ∈ F_M has a head normal form (BEKW Q10), then every t with
[t]_P ∈ F_P is productive. *Proof.* Let G = {t : [t]_P ∈ F_P}. For t ∈ G the fact gives [t]_M ∈ F_M, so t has an hnf h
(Q10); [h]_P = [t]_P by Lemma 3, so the components of h lie in G by (iii). By coinduction every node of BT(t) lies in G
and has an hnf: BT(t) has no ⊥. ∎
Hence Q10 ∧ (completeness: [t] = ⊥_P ⇒ t not productive) ⇒ C6. **Since Theorem Q10, the soundness half of C6 is PROVED: every term whose P39 class is in F_P is
productive.** (Only this direction holds: C6 says nothing about head
normal forms of the 17 joint classes (⊥_P, F_M), so C6 does not imply Q10 — audit correction.) The
completeness half remains OPEN: ⊥_P splits into 18 joint classes, only one of which (⊥_P, ⊥_M) is certified hnf-free
(Theorem A); for the other 17 one must show that the ⊥_P path forced by (iii) reaches a node without hnf.
**Completeness half, COMPUTATIONALLY CERTIFIED for all terms ≤ 19 leaves (E23):** for every t with |t| ≤ 19 and
[t]_P = ⊥_P, an explicit Böhm-tree path leads to a node whose M35 class is ⊥ (no hnf by Theorem A) — an unconditional
certificate of non-productivity, independent of step budgets. Hence, for |t| ≤ 19, C6 holds (using Theorem Q10)
(Proposition Q). Beyond 19 leaves: 100,000 random terms with 20–36 leaves agree in both directions (E24); the closure at contexts ≤ 7
reproduces P39 exactly (E22). **Conjecture C7 (shallow ⊥):** if t is not productive, BT(t) has a node without hnf at depth ≤ |t| − 3
(tight: S^{k}(SSS(S(SS))(SS)), |t| = k + 7). C7 + C2 would make productivity decidable by bounded exploration even without
C6; a proof of C6's completeness half for all t still needs a well-foundedness argument.

---------------------------------------------------------------------------------------------------
## Theorem P2 (Böhm-tree finiteness counts modulo 2) — PROVED and MACHINE-CHECKED in Lean 4 (lean/P2_Parity.lean, 2026-10-27)
*Lean (main agent, 2026-10-27).* `P2 : ∀ j, BTFin (args (T j)) ↔ (j % 2 = 0 ∨ j = 1)`, with BTFin the inductive Böhm-tree
finiteness over the deterministic head machine (a ⊥ leaf when no hnf is ever reached). Axioms: propext, Classical.choice,
Quot.sound. The M35 facts (S-identity over all 35³ triples, closure of the class range, hnf shapes, the fixed point
pre(5) = pre(4), the four ⊥-classes) are checked by the kernel with `decide +kernel` over a base-35 bignum encoding of
the table, and the checkers depend on NO axioms. Theorem A is in lean/TheoremA_M35.lean. The Lean proof follows the hand
proof below step by step: uniqueness of the hnf (`hnf_unique`, `btfin_hnf`), the run lemma (`run_spine`), the
head-run lemma (`head_run_T`), the class facts (`pre_fix`, `W_notF`), the odd seed (`not_bt_path`, by induction on
the finiteness derivation) and the induction on j.
Let X = SSS, Y = SS and T_j = S S^{×j} X Y, the S-term whose head S has the j+2 spine arguments
[S, …, S (j times), X, Y]; in left-spine notation T_j = S^{j+1}(SSS)(SS), so T_j = E[P^j[S]] with the pumping context
P[u] = u S and the outer context E[u] = u X Y. **Then BT(T_j) is finite iff j is even or j = 1.** Equivalently the family
t_k = S^{k+3}(SSS)(SS) has a finite Böhm tree iff k is even.
*Proof.* (1) *Run lemma.* For m ≥ 2 the head machine maps [S^{×m}, c] ++ R ⇒^{m−1} [c, B_{m−1} c] ++ R, where B_i is the
left spine of i leaves S (one step for m = 2; for m ≥ 3 the first step gives [S, SS, …] and each further step
[S, B_i, S, …] ⇒ [S, B_{i+1}, …], until [S, B_{m−1}, c, …] ⇒ [c, B_{m−1} c, …]).
(2) *Head-run lemma.* For j ≥ 2, T_j →^{j+3} S (S Y T_{j−2}) (T_{j−2} (S Y T_{j−2})): by (1) [S^{×j}, X, Y] ⇒^{j−1}
[X, B X, Y] with B = B_{j−1}, then ⇒ [S, S, Y, BXY] ⇒ [Y, SY, BXY] ⇒ [S, BXY, SY(BXY)] ⇒ [SY(BXY), BXY(SY(BXY))], and
B X Y = T_{j−2}. (Checked concretely for j = 2..8.)
(3) *Certified no-hnf facts.* In M35, [T_j (S Y T_j)] = ⊥ for j = 0 and for all j ≥ 2 (computed for j ≤ 5; the class of the
prefix S S^{×j} reaches a fixed point of x ↦ x·S at j = 4, so all later classes coincide). By Theorem A these terms have
no head normal form. For j = 1 the class is head-normalising.
(4) *Odd seed.* Let V_0 = T_1 and V_{r+1} = S Y V_r. Symbolic head runs (V opaque) give
T_1 V →³ S (X Y V) (V (X Y V)), X Y V →³ S (S Y V) (V (S Y V)), and V_r V' →² S (V_{r−1} V') (V' (V_{r−1} V')) for r ≥ 1
(all three verified with code/symb.py, V opaque).
Hence BT(T_1 V_1) contains the path T_1 V_r → X Y V_r → V_r V_{r+1} → V_{r−1} V_{r+1} → ⋯ → V_0 V_{r+1} = T_1 V_{r+1} for all
r ≥ 1 (first, second, then first components): an infinite path (a self-incrementing counter, as in Theorem C).
(5) T_0 = S X Y and T_1 →* S Y (X Y) →* S Y (S (SS) (S (SS))) are normalising, so BT(T_0), BT(T_1) are finite.
(6) By (2), for j ≥ 2: BT(T_j) = S · (S · BT(Y) · BT(T_{j−2})) · BT(T_{j−2}(S Y T_{j−2})). If j ≠ 3 the last factor is ⊥ by
(3), so BT(T_j) is finite iff BT(T_{j−2}) is; for j = 3 the last factor is BT(T_1 V_1), infinite by (4). Induction from
(5): even j give finite trees, odd j ≥ 3 give infinite ones. ∎
(Independent oracle check: t_k for k = 0..40, depth cap 3000: pattern 1010…1, exact.)
**Consequences.** (i) **Conjecture C4 (Böhm-tree finiteness is counter-free) is REFUTED**: along the pumping family
E[P^j[S]] with a one-leaf pumping context, finiteness alternates with period 2. The earlier tests missed it: E12's outer contexts had
≤ 3 S's (this one, □ X Y, has 5), and E11 pumped only wrapper families (audit correction of the earlier "9"). (ii) The mechanism is intrinsic to the head machine: each Böhm-tree round strips two
S's from a spine run ([S^{×m}, …] feeds m−2 of them into B_{m−1}), so spine length is read modulo 2. (iii) For the prize
this removes counter-freeness as a route to non-universality; what remains is regularity (decidability) — see E25.

## Proposition Q′ (one half of the 131-class BT-finiteness model) — PROVED (was conditional on Q10; unconditional since Theorem Q10)
Let B131 be the learned model (data/model131_btfinite.txt), F_fin its 98 "finite" classes. *Certified facts
(code/modelstats.py):* B131 is an S-model; s x y ∈ F_fin ⟺ x, y ∈ F_fin and s x ∈ F_fin ⟺ x ∈ F_fin; [S] ∈ F_fin; in the
sub-magma of B131 × M35 × P39 generated by the S-classes (416 elements) no element pairs a non-F_fin class with ⊥_M.
*Claim.* If every term with [t]_M ∈ F_M has a head normal form (Q10), then every t with [t]_B ∉ F_fin has an infinite Böhm
tree. *Proof.* [t]_M ≠ ⊥_M by the joint fact, so t has an hnf h (Q10); [h]_B = [t]_B ∉ F_fin (Lemma 3); h ≠ S, and by the
closure facts some component of h is again outside F_fin. Iterating (taking at each node its head-reduction hnf, which exists by Q10) gives an infinite path of Böhm-tree
nodes, each with an hnf. ∎ (Audit: correct; P39 is not needed — the sub-magma of B131 × M35 generated by the S-classes
already has the joint fact, 221 elements; ⊥_M occurs only together with B-class 50, which is a finite class.)
The other half (F_fin ⇒ finite Böhm tree) needs a well-foundedness argument, as for C6; it is **certified** for every
term ≤ 19 leaves by explicit budget-free exploration (E28). **Conjecture C8:** B131 decides Böhm-tree finiteness for all closed S-terms (⇒ decidable in
linear time; regular but not star-free, by Theorem P2).
**Scope note (finite models vs decoders).** A finite S-model only decides conversion-invariant properties, i.e. properties
of the Böhm tree's *shape* (labels S/⊥). A Wolfram-style decoder that reads the *syntax* of Böhm-tree node terms (e.g. "the
node equals C_q[⟨a⟩,⟨b⟩]") is not conversion-invariant, so regularity results like C6/C8 cannot exclude universality through
syntactic decoders; Theorem O covers the exact-checkpoint part of that space (bounded cost, unentangled counters).

## Conjecture C9 (finite-model conjecture for Böhm trees of S-terms) — CONJECTURAL, strongly supported
Every MSO-definable property of Böhm trees of closed S-terms is recognised by a finite S-model (a finite magma satisfying
the S-identity, with an accepting set). Evidence: seven properties — HN, productivity, finiteness, leftmost/rightmost/LO path infinity and branching infinity
(35, 39, 131, 36, 19, 204, 423 classes; E26, E29, E30) — several counting modulo 2 (so the right class is "regular",
not "star-free"), none counting modulo anything else. C9 ⇒ C5′ ⇒ (Proposition P) no universal emulation with
a Böhm-tree-shape halting signal. It does not address decoders that read node syntax (scope note above).
*Why C9's proofs are hard (precise).* In each model the hard direction is a termination statement (Q10: accepting M35
class ⇒ the head run halts; C6: ⊥_P ⇒ the search for ⊥ halts; C8: finite class ⇒ the Böhm-tree exploration halts). The
naive logical relation over the finite magma — "t ∈ ⟦c⟧ iff t has an hnf and t u ∈ ⟦cd⟧ for all u ∈ ⟦d⟧" — is not a
monotone clause (⟦·⟧ occurs negatively, with no type stratification), so it does not define ⟦·⟧ by Knaster–Tarski.
This does not rule out step-indexed or mixed-variance constructions, which have not been tried (audit correction: the
earlier text called this a failure in general and wrongly cross-referenced FAILED_APPROACHES item 3, which is about size
induction).
**Conjecture C10 (parity is the only counting).** For every MSO property of Böhm trees of S-terms, the syntactic monoid
of the corresponding finite S-model has only trivial or Z/2 subgroups: along any pumping family E[P^k[D]] every such
verdict is eventually periodic with period 1 or 2. Evidence: all elements of the five learned monoids (E26); Theorem P2
shows period 2 does occur.

---------------------------------------------------------------------------------------------------
## Proposition R (for modular emulations, halting reduces to infinity of a Böhm-tree path) — PROVED (elementary; the
## modularity hypothesis carries the content)
*Setting (made precise after the audit).* Böhm-tree nodes are the actual terms produced by head reduction: the next node
is a component of the head-reduction hnf of the current one. A path rule ρ chooses a component at each node (ρ = leftmost:
always the first; rightmost: always the last; LO: the first unless it normalises, else the second — the path
leftmost-outermost evaluation follows). A machine U is *emulated along ρ* if there are a computable encoder w ↦ t_w and
closed terms N_κ for configurations κ such that the ρ-path of BT(t_w) visits N_{κ_0}, N_{κ_1}, … for the run
κ_0 → κ_1 → … of U on w, at strictly increasing depths (any decoder, syntactic or not, may be used to read κ_i off
N_{κ_i}). The emulation is *modular at halting* if there is a **computable** w ↦ t′_w whose ρ-path visits N_κ for the
non-halting configurations of the run and **Ω N_κ** for the first halting one, at strictly increasing depths, where Ω is a
fixed closed S-term without head normal form (e.g. any term whose M35 class is ⊥). Nothing here shows that an arbitrary
emulation can be made modular — that is an assumption, and it is the substantive one.
**Claim.** For a modular emulation along ρ: U halts on w ⟺ the ρ-path of BT(t′_w) is finite and ends in ⊥.
(Audit 3: the Claim is about the modular encoding t′_w, not t_w.)
*Proof.* If U halts, the path reaches Ω N_κ, which has no hnf (Ω is in head position): the path ends in ⊥. If U does not
halt, the path visits infinitely many configuration nodes with ≥ 1 step between them, so it is infinite. ∎
**Corollary R1.** If for ρ the property "the ρ-path of BT(t) is infinite" is decidable, then no universal machine (one
with undecidable halting problem) has an emulation along ρ that is modular at halting — whatever decoder is used.
**Status of the hypothesis: not proved for any ρ.** Evidence only: learned finite models for ρ = leftmost (36 classes),
rightmost (19) and LO (204), each agreeing with the budgeted oracle on every term up to 16–18 leaves (E26, E29; audit
extended the leftmost/rightmost censuses to 16 leaves, 0 disagreements). For ρ = LO the replacement N_κ ↦ Ω N_κ cannot
change earlier choices of the path (the path enters a first component only when it does not normalise, and a step into
the second component depends only on the untouched first one) — checked by the audit.
**Scope.** Not covered: emulations that are not modular in the above sense; configurations that are not single node terms
on one fixed path (e.g. snapshots of leftmost-outermost reducts whose already-normalised left context carries data, or
several configurations inside one head reduction); and every ρ whose path-infinity is not proved decidable — currently
all of them. So R1 presently excludes nothing unconditionally.


---------------------------------------------------------------------------------------------------
## Independent audit (one adversarial subagent, PROOF.md sections Lemma 8–12, N*, Theorem O, Proposition Q only)
Verdicts: no counterexample to any main claim. Theorem O: three fillable gaps (reversed size argument in (2′); missing
"x and y both in s" case in (2); "read" must include the spine split at Böhm-tree nodes) plus two misstatements (O1's
Minsky parenthesis; Remark (ii)'s "cost < a") — all repaired above. Lemma 8(ii), Lemma 9: termination hypothesis was
implicit; Lemma 9(a) is false for divergent runs (example [Ω, S, x, w]) — hypothesis added. Lemma 10: statement correct,
proof replaced by the termination-free invariant J. Lemma 11: needs t closed — added. Theorem N*: correct; presentation
fixed (junction node, "do not increase", Layer-lemma hypothesis, POT defined; the separate maxima are also monotone).
Lemma 12: correct (with the extended "read"). Proposition Q: correct; its finite fact was recomputed independently;
the surrounding equivalence was overstated and one C6 sentence was stale — both fixed. Audit scripts:
scratchpad/audit/ (q_check.py, nstar_check.py, nstar_random3.py, lemma10_9_check.py, lemma11_check.py,
lemma9a_example.py, c6_spot.py). Dates in this file follow the session log (the overnight run crossed midnight).

## Note on Question 10 via intersection types (2026-10-25) — reformulation, not a proof
Interpret S-terms in the lazy intersection type system (types ω, σ→τ, σ∧τ; CONV := ω→ω means "has a head normal form";
S : (σ1→σ2→τ)→(σ3→σ2)→(σ1∧σ3)→τ plus the convergence types of S, S x, S x y). Soundness (t : CONV ⇒ t has an hnf) is
the standard reducibility argument and is well-founded because types are finite trees. Define for each M35 class the
*principal type* T_c = CONV ∧ ⋀_{c2 : c·c2 ∈ F} (T_{c2} → T_{c·c2}). Then (checked by hand) S : T_s and the application
rule gives t1 t2 : T_{c1·c2} from t1 : T_{c1}, t2 : T_{c2}, using only the S-identity of M35 — so every term with
[t] ∈ F gets the type T_[t] ≤ CONV. But T_c is a **recursive** type (classes recur in argument positions), for which the
reducibility proof does not apply; finite unfoldings T_c^{(d)} fail at S by one level (z is used twice: x z needs z at
depth d+1). Hence: **Q10 ⟺ soundness of the recursive type assignment {T_c}** — an exact reformulation that pins down the
difficulty (negative recursion through duplicated arguments), not a proof.

## Second independent audit (Theorem P2, Propositions Q′ and R, C9 paragraph)
Theorem P2: CORRECT (every step re-derived; head-run lemma and odd seed checked for j ≤ 40 and r ≤ 24; M35 certificate
recomputed; finite trees for even j ≤ 20 have 6 + 5j/2 nodes). Proposition Q′: CORRECT (facts recomputed independently;
P39 unnecessary). Proposition R: definitional gaps and an overclaiming title/scope — rewritten above; R1 excludes nothing
unconditionally until some path-infinity property is proved decidable. C9 paragraph: overstated "fails" and a wrong
cross-reference — corrected. Dates normalised to the system date (2026-10-25). Audit scripts: scratchpad/audit2/.

**Remark R2 (decoders that read finished output need no modularity).** Leftmost-outermost evaluation builds BT(t) in
depth-first order, leaving finished subtrees behind as normal forms. Suppose an emulation signals halting by the
appearance of a finished subtree (finite and ⊥-free) whose shape lies in a regular tree language R. Then "U halts on w"
is the MSO property "some node of BT(t_w) roots a finite, ⊥-free subtree accepted by the automaton for R". So, by the
argument of Proposition P, C5′ (MSO-decidability of Böhm trees; implied by C9) excludes every such emulation, whatever the
encoder and without any modularity assumption. What C9 does not cover is decoders that read *unfinished* node terms
(the active, not-yet-normalised part); for those, Proposition R needs modularity.

## Question 10 via ranking functions (BEKW's semantic-labelling suggestion) — a precise negative result
Encode head reduction as the root-only rewrite system on configurations [e1,…,em] (head S implicit) and label every
element with its M35 class and the right-multiplication monoid element λ of the elements below it (209 elements).
**Claim (COMPUTATIONALLY CERTIFIED, code/q10_lp*.py).** There is no ranking function of the form
Φ = Σ_i W(class(e_i), λ_i)·|e_i| (|e| = leaves, W ≥ 0, W ≥ 1 on every element that is opened in some non-⊥
configuration) that strictly decreases along all head steps of non-⊥ configurations: the LP is infeasible already with
only the y- and z-constraints (y·z replaces y; z is duplicated), i.e. the obstruction is the duplication of the third
argument, not the spine of the opened element. (The necessary fixed-point test passes — no λ∘ρ_{yz} = λ — so the
conflict comes from longer cycles of below-contexts.) Consequence: a proof of Q10 must distinguish duplicated copies
that are later opened from copies that stay passive; size-counting with finite labels cannot.
*Addendum (ranking functions).* With three labels (above-prefix class, class, below-context — the above-prefix of
untouched elements is invariant by the S-identity) the symbolic LP is still infeasible (code/q10_lp3.py), while the same
ansatz IS feasible on all 17,004 actual head steps of terminating runs up to 11 leaves (code/q10_data.py, 2 or 3 labels).
So finitely labelled size-potentials fit small terms but provably cannot certify Q10 for all terms.

## Proposition S (leftmost-path infinity from a computable path bound + Padovani's theorem) — PROVED (reduction), C11 CONJECTURAL
_Audit 3 (2026-10-25): title narrowed — this route still needs a decidability argument (with Padovani's theorem, C11's
computable form is equivalent to the hypothesis of Corollary R1 for ρ = leftmost); it avoids only Question 10 and the
learned models._
**Conjecture C11 (fast-or-never for leftmost paths) — linear form REFUTED (for all k, proof below); computable form open.**
Originally: if the leftmost path is finite its length is ≤ |t| + c. **Counterexample family:** X_{−1} = S, X_0 = SSS,
X_{j+1} = S S X_j (k comb layers SS(·)), t_k = SSS X_k SS, |t_k| = 8 + 2k.
**Theorem.** For every k ≥ 0 the leftmost path of BT(t_k) is finite, ends at the leaf S, and has exactly k² + 3k + 3 edges.
*Proof (found by audit 3, re-checked by hand; the opaque R is never opened).* Put W = S X_k S and R_j = X_j S W S. Head
reduction gives these first components (each line is one path edge):
 X_j S (SS) R ↦ X_{j−1} S (SS) R (j ≥ 0, four head steps);  S S (SS) R ↦ R (one step);
 t_k ↦ X_{k−1} S (SS) R_{k−1} (ten steps);  R_j ↦ X_{k−1} S (SS) R_{j−1} (j ≥ 0);  R_{−1} = S S W S ↦ S.
So t_k reaches R_{k−1} after k + 2 edges, each R_j (j = k−1, …, 0) reaches R_{j−1} after k + 2 edges, and R_{−1} ends the
path in one edge: (k + 2) + k(k + 2) + 1 = k² + 3k + 3. ∎ (Independently recomputed for k = 0…12: 3, 7, 13, …, 183.)
There are k + 1 rounds of k + 2 nodes; per round the outer counter loses one SS layer (node sizes fall by 2; at k = 2:
24 22 20 16 | 22 20 18 14 | 20 18 16 12). So finite paths can be quadratic in |t| (nested counters plausibly give more).
The surviving statement — a computable bound f — is, given Padovani's theorem, equivalent to decidability of path
infinity, so this route is not easier than the direct one.
Evidence (code/lpathlen.py, all terms): maximal finite length 2, 3, 4, 5, 6, 8, 9, 10, 11, 13 for |t| = 3…12 (attained by
S(S(⋯S(SSS(S(S(SS)))S)⋯)) with nested S(·) layers for n = 8…11; at n = 12 the maximum 13 is attained by 13 terms, t_2
among them); the unfinished cases (1, 2, 5 at 10, 11, 12 leaves) are exactly the terms the 36-class model calls
infinite. Caveat: lpathlen.py counts head-step budget exhaustion as ⊥, unsound in principle; audit 3 recomputed with
budget exhaustion as "unknown" and certified every such case ⊥ by its M35 class (Theorem A), so the numbers stand.
**Claim.** C11 (with any computable bound f in place of |t| + c) + decidability of head normalisation (Padovani, *A Lambda
Calculus Satellite* Ch. 7, a published theorem whose proof we have not seen) ⇒ "the leftmost path of BT(t) is infinite"
is decidable. *Proof.* Walk the path for f(|t|) + 1 steps: at each node decide whether it has an hnf (Padovani); if not,
the path ends in ⊥; if so, compute the hnf by head reduction (it terminates) and continue with the first component (a
node with no component ends the path). By C11, a path still unfinished after f(|t|) steps is infinite. ∎
**Corollary.** C11 + decidability of head normalisation (Padovani; proof not checked by us) ⇒ (Proposition R,
ρ = leftmost) no universal machine has an emulation along leftmost Böhm-tree paths that is modular at halting — with no
appeal to Question 10 or to any learned model. The prize-relevant gap on this route is exactly C11 plus the modularity
hypothesis.

## Lemma 13 (structure of a minimal counterexample to Question 10) — PROVED ((iii) conditional on C2)
_Audit 3 (2026-10-25): (ii) restricted to argument-internal occurrences (t itself and its spine prefixes are never inside
a list element, so never "read"); (iii) now quotes C2 correctly._
Let t = S e1…em be a counterexample to Q10 ([t]_M35 ∈ F, no head normal form) of minimal size (|t| ≥ 20 by Theorem B).
Then (i) every proper spine prefix S e1…ej of t has a head normal form; (ii) every subterm occurrence u lying inside (or
equal to) one of the arguments e1, …, em that is not of minimal size in its M35 class is read (some residual of it is
opened, in the sense of Lemma 11) during the infinite head run of t; (iii) if moreover C2 holds, all such occurrences are
read within the first 2|t| head steps.
*Proof.* (i) A proper prefix has an F-class (⊥ is left-absorbing) and is smaller. (ii) Replace u by a smaller term u′ of the
same class: the class of the whole is unchanged (M35 is a congruence) and the result t′ is smaller, so t′ has an hnf. Head
reduction never rewrites inside a list element, so every residual of u is an exact copy of u; if no residual of u were
ever opened, the head runs of t and t′ would correspond step by step (residuals of u replaced by residuals of u′), so t′
would diverge too — contradiction. (iii) The runs of t and t′ correspond until a residual of u is first opened; by C2, t′
halts within 2|t′| ≤ 2|t| − 2 steps, and t does not halt at all, so u is read before that time. ∎
Consequence: the infinite run reads every argument-internal occurrence that is not size-minimal in its class — in
particular every one with ≥ 9 leaves, since every M35 class has a member with ≤ 8 leaves (audit 3 computation) — and,
under C2, within 2|t| steps: divergence cannot be caused by a large part that lies dormant. (Not yet a contradiction —
after everything is read, copies keep the run going.)

## Lemma 14 (quantitative typing: an S-term is typable ⟺ it head-normalises) — PROVED (standard technique, adapted)
*Types* τ ::= o | M → τ with M a finite multiset of types. *Axioms for S:* o, [] → o, [] → [] → o, and for all k ≥ 0
and all M1, N1, …, Nk, B, C1, …, Ck:  [M1 → [C1,…,Ck] → B] → [N1 → C1, …, Nk → Ck] → (M1 + N1 + … + Nk) → B  ("reduction
form", weight k). *Rule:* from t : M → τ and one derivation of u : σ for each element σ of M (with multiplicity) infer
t u : τ. The weight of a derivation is its number of application nodes plus the weights of its reduction-form axioms.
(a) *Subject reduction with decrease.* A derivation D of S a b c r1…rm : τ yields a derivation of a c (b c) r1…rm : τ of
weight w(D) − 1. *Proof.* The head S takes ≥ 3 arguments, so its axiom has the reduction form (the value types end in o
after ≤ 2 arrows): a has one derivation of M1 → M2 → B, b has k derivations of N_j → C_j, c has |M1| + Σ|N_j|
derivations. Build a c : M2 → B from a's derivation and |M1| of c's, b c : C_j from b's j-th and |N_j| of c's, then
(a c)(b c) : B and the applications to r1…rm; every subderivation is used exactly once. Application nodes: m + 3 before,
m + 2 + k after; the head axiom of weight k disappears. ∎
(b) Hence a closed S-term typable with any type has a head normal form, reached within w(D) head steps.
(c) Conversely every head-normalising term is typable with o: type its hnf (S : [] → [] → o etc., components untyped) and
expand backwards along the head run — the converse of (a); `code/nitypes.py` builds these canonical derivations.
*Remark.* (b) uses the derivation weight, not an induction on types, so it holds verbatim for infinite (e.g. recursive)
types as long as derivations are finite trees. That is what makes typing a candidate certificate for Q10 where finitely
labelled size potentials (q10_lp*.py) and idempotent recursive types (note above) fail: an unused copy of a duplicated
argument simply receives the empty multiset.

## Proposition T (type certificates for Question 10: no finite type set suffices) — PROVED; search data COMPUTATIONALLY CERTIFIED
For a set Θ of types put V(S) = {axiom types in Θ} and V(t u) = {τ ∈ Θ : some (M → τ) ∈ V(t) has every element of M in
V(u)}. By Lemma 14 every τ ∈ V(t) is derivable for t, so "o ∈ V(t) for every t with [t]_M35 ∈ F" would prove Q10, and for
finite Θ this is a finite check on the magma generated by (s, V(S)) in M35 × P(Θ) (`code/nicert.py`).
**No finite Θ works.** The left combs S^k (k S's, left-associated) all head-normalise (H(S^{k+1}) = App(S S X, S) =
S S (X S) by Lemma 2(b), from H(S^4) = S S (SS)) and lie in F (class 12 for k ≥ 5, since 12·s = 12). In any derivation
of S^k : o the head S has a type with k − 1 arrows, so Θ would need types of unbounded length. ∎
*Search data.* With Θ grown from the canonical derivations of all F terms ≤ 7 leaves and then repaired with the canonical
types of failing representatives, the generated magma stays small (58–72 elements), but 6–7 F elements keep failing, in
classes 12, 21, 24, 26, 28, 29, 31 — the cyclic core of the abstract call graph (Partial reduction of C1) — and each
repair adds deeper types (depth 8 → 20 in 7 rounds). The S-types needed by S^k are τ_0 = [] → [] → o,
τ_{j+1} = [τ_j] → [] → T_j with T_0 = [] → o, T_j = [τ_{j−1}] → T_{j−1}: unbounded, and the reduction-form axiom repeats
its tail B in two places, so a plain regular-tree-language description of V(S) is not obviously possible either.
**Status:** a type certificate for Q10 must describe tails schematically (e.g. tail-polymorphic or pushdown-style types);
whether one exists is open. Canonical-type census (first version of `code/nitypes.py`, counting only the types of
argument occurrences, i.e. without head-S and spine-prefix types): distinct types over all F terms with ≤ n leaves grow
1, 1, 1, 2, 3, 6, 15, 31, 58, 69, 73, 77 (n = 1…12), maximal depth 14 — slow growth, driven by the long-spine families.

## Conjecture C12 (bounded re-opening) — CONJECTURAL; EXPERIMENTALLY SUPPORTED (exhaustive to 13 leaves)
In the head run of a head-normalising S-term, every application occurrence of the original term is opened (is the base
of the opened element, in the provenance machine of `code/opencount.py`) at most twice, and every leaf occurrence at most
four times.
Evidence: all 224,716 M35-F terms with 3–13 leaves (all head-normalising, Theorem B) — maxima 2 (application) and 4 (leaf;
reached only at 9 and 10 leaves, 3 elsewhere); about 2,000 random F terms each at 20, 30 and 40 leaves (from 3,000 samples
each) stay within 2 / 3 (but
their runs are short, ≤ 14 steps). Diverging runs open some occurrence 31–124 times within 200 steps (8–11 leaves).
Consequence: C12 ⇒ a head-normalising term reaches its hnf within 2(|t| − 1) + 4|t| = 6|t| − 2 steps (each step opens
exactly one occurrence) ⇒ head normalisation is decidable in linear time (a weak form of C2, and of Padovani's theorem).
It describes why terminating runs are short — each part of the term is used boundedly often, like the multiplicities in
Lemma 14 — but it is not by itself a route to Q10.


---------------------------------------------------------------------------------------------------
## Prize target, made precise (2026-10-25, evaluation-order pivot)
*Official notion (Wolfram 2021 announcement).* Universality = an encoder E (machine, input) ↦ S-term, an evaluation order,
a detector and a decoder, none of them universal (bounded-time suggested), such that the S-evolution emulates a universal
system; weakest variant ("weak"): some evaluation path performs any deterministic computation; detectors may act on some
or all branches. A disproof may show the evolution is 'solvable'/modulations die out; an intermediate degree also counts.
*Hidden computation (PROVED, elementary).* If the evaluation order may be any polynomial-time function of the current
term, the question trivialises: take E(M, w) = a fixed divergent term that keeps producing fresh, independent redexes,
let the order replay the history recorded in the term (which redexes were fired), simulate M for one more step, and fire
a redex in a 'yes' or 'no' region; the detector reads the regions. All computation is in the order. So the order must be
a fixed rule that cannot compute by itself.
*Working target W_reg.* S is weakly universal if there are a regular (finite-tree-automaton/MSO-definable) redex-selection
rule σ, a regular detector D and a homomorphic encoder E with: M halts on w ⟺ some term on the σ-path of E(M, w) lies in
D. Non-universality ⟸ for all regular σ, D: {t : the σ-path of t meets D} is decidable (or at least not r.e.-complete).
Standard orders (leftmost-/rightmost-, outermost/innermost) are regular. The leftmost Böhm-tree walk with a syntactic
detector on node terms is an instance (it is computed by leftmost-outermost reduction restricted to the leftmost path).
*Where the current theory stands against W_reg.* Conversion-invariant detectors reduce to Böhm-tree properties (finite
models; partly proved); syntactic detectors along head/leftmost paths are excluded only for bounded-cost two-counter
designs (Theorem O); nothing covers innermost orders or syntactic detection in the full re-execution regime — and the
reloading counters of 'Reload cycles' live exactly there.

## Theorem SI (detectors that respect convertibility are useless, under every evaluation order) — PROVED (elementary)
Let D be a regular set of S-terms (recognised by a finite tree automaton) that is closed under convertibility
(t ∈ D, t =_w t′ ⇒ t′ ∈ D). Then there is a finite S-model M_D with D a union of its classes; consequently, along ANY
reduction sequence t = t_0 → t_1 → … (any evaluation order, any branch of the multiway system) t_n ∈ D ⟺ t ∈ D, and
membership is decided in linear time on the initial term.
*Proof.* The syntactic congruence ≡_D (t ≡ t′ iff C[t] ∈ D ⟺ C[t′] ∈ D for all one-hole contexts C) has finite index
because D is regular. Since =_w is a congruence and D is =_w-closed, C[S x y z] ∈ D ⟺ C[x z (y z)] ∈ D, so
S x y z ≡_D x z (y z): the finite quotient magma satisfies the S-identity on all elements (every element is the class of
a term), i.e. it is a finite S-model, and D is a union of classes. Lemma 3 gives invariance along reductions. ∎
*Consequence for the prize.* A universal emulation — for any evaluation order, weak or strong — must use a detector that
does NOT respect convertibility, i.e. one that reads syntax which conversion can change. All finite-model results
(M35, P39, B131, L36, …) only constrain convertibility-respecting observations; the open question is entirely about
syntax-sensitive detection along particular evaluation orders.

## Attempt U (universality via programmable counters on leftmost walks) — no construction found
Exact symbolic interpreter for nests N = W^n(B) with symbolic n (code/nestwalk.py; opening branches on n = 0 / n ≥ 1;
W-applications to nests folded back): it reproduces the reloading family exactly — (i ≥ 1, k ≥ 1) ↦ (i − 1, k),
(i = 0) ↦ (k, k + 1) for W = SS, B = S(SS)(SS), tail S. Search over two-slot nodes N_i N_k R: with W = SS, bases ≤ 5
leaves, tails ≤ 3 leaves, only 4 distinct counter programs exist (plain countdowns and that one reloader); with wrappers
S, SS, SSS, S(SS), bases ≤ 4 leaves, tails ≤ 2 leaves and state changes allowed, 267 plain countdown transitions and 8
reload-at-zero transitions whose target families only count down and stop. No family realises two independently
controlled counters with zero tests and control states (the Minsky-machine primitives). This is a search result in a
natural design space, NOT a proof that no universal encoding exists.

## The uncovered regime: infinite head runs under leftmost-outermost evaluation (2026-10-25) — analysis
*Why it is open.* For a term without hnf, leftmost-outermost evaluation never leaves head position, so its whole evolution
is one infinite head run. Lemma 8 (data conservation) and Lemma 10 (no junk-free rotation) hold for every head run, but
Lemma 9 ("code cannot write into data") and Lemma 8(ii) need the run to TERMINATE (audit note: the divergent run on
[Ω, S, x, w] writes x into S x). All anti-tag/anti-register results were per Böhm-tree step (terminating runs), and by
Theorem Q10 every call on a diverging run has class ⊥, so the finite models say nothing there either. This is the one
regime where a syntax-sensitive detector could see computation that no current theorem excludes.
*What the runs look like (code/opcodes.py; opcode = spine length of the opened front element, capped at 3).* All 892
hnf-free terms with ≤ 10 leaves, 6,000 head steps: 462 eventually periodic, 256 a single linear counter (the lengths of
the 2-runs satisfy L_{j+p} = L_j + c_{j mod p} with every c ≤ 1), 31 driven by other opcodes, 143 periodic up to rare
insertions (apparently a counter in another opcode). Example SSS(S(SSS))S: blocks 39,41,41 | 40,42,42 | 41,43,43 | …
(one counter, +1 per period), element sizes growing to 10^4–10^5 within 250 steps. No run showed two interacting
counters. Self-reproducing code loops with clean nests do not occur (code/loopsearch.py, headcounters.py: in head runs
nests acquire appended arguments N_{k−1}·c and never return clean).
*Status.* No construction; no theorem. Two concrete continuations: (a) a structure theorem "every infinite head run is
eventually a finite composition of linear counters" (would make regular syntax-sensitive detection along
leftmost-outermost evaluation of hnf-free terms decidable via counter-language arguments); (b) engineering an infinite
head run with two interacting counters and data-driven zero tests (the Minsky primitive), which would be the first real
step towards weak universality.

*Route (b) first result (2026-10-25): class information says nothing about diverging runs.* On a diverging head run every
call has class ⊥ (Theorem Q10), and the chain graph restricted to ⊥ (refills allowed only when the nested computations
terminate, i.e. a, a·β ∈ F) has one strongly connected component of 5,550 states containing 1,251,602 refill edges (171
refill self-loops) — so the certificate method of Theorem Q10 cannot classify infinite head runs; a structure theorem
needs invariants finer than any finite S-model (Theorem SI shows why: those only see convertibility). Candidate framework:
higher-order / collapsible pushdown systems, where reachability of regular configuration sets is decidable — the head
machine is a stack of trees without environments, but its nesting depth is unbounded, so no fixed-order simulation is
known.

## Universality route: counter transfers inside one infinite head run (agent U, 2026-10-25) — PROVED (audit 6: construction correct; Theorem U correct with fixes)
*Construction.* Om = S(SSS)S(SSS), q = SS; target counter M_0 = SSS, M_{m+1} = S S q (S M_m); source counter
P_0 = S(SSS)Om, P_k = S(S(S(S P_{k−1}) V1)) V2 with V1 = S S q, V2 = S; Φ(k, m) = S P_k S M_m (M35 class ⊥; smallest
member Φ(0,0) = S(S(SSS)(S(SSS)S(SSS)))S(SSS), 17 leaves). Key gadget ("head-style" nest: predecessor first, closed
constant after): [S(S P′)V, t1, t2] →² [P′, t2, V·t2, t1·t2] — one unit is written cleanly into the target, the duplicate
t1·t2 sinks into a frozen tail. Exact rules (symbolic, opaque predecessors/tape elements, all counter values):
 R1 (k ≥ 1) [P_k, x, M] →⁴ [P_{k−1}, V2·M, V1·(V2·M), …];  R1z [P_0, x, M] →³ [M, S·M, Om·M, x·M];
 R2 (j ≥ 1) [M_j, t1, t2] →³ [M_{j−1}, t2, q(S M_{j−1})·t2, t1·t2];  R2z [M_0, t1, t2] →² [t2, S·t2, t1·t2];
 R3 [L·Y′, d, F] →² [Y′, (S e)·Y′, F, d·F] (L = q·(S e));  R3z [Om·Z, d, F] →¹ Om's spine on top (runs forever).
*Classes (audit 6):* [P_0] = 24, [P_k] = 28 (k ≥ 1), [M_0] = 3, [M_m] = 28 (m ≥ 1); these recurrences are functions on the
35 classes, so [Φ(k, m)] = 33 (no hnf) for ALL k, m. Audit 6 re-derived every rule with its own symbolic machine (no opaque
element is opened; R1 also leaves M·(V2·M) and x·M below), re-derived 4k + 5m + 6, and matched 13 concrete runs at every
macro boundary (e.g. (12,7): 149 steps, (30,11): 331, (0,40): 206); the frozen tail is never read.
*Program realised by the single infinite head run:* while P > 0 {P−−; M++}; while M > 0 {M−−; Y++}; while Y > 0 {Y−−};
loop forever — data-driven zero tests and three control phases, reaching the final loop after 4k + 5m + 6 steps
(m = k + m0); concrete checkpoints verified for k ≤ 8, m0 ≤ 5 (re-run 2026-10-25: all True). Straight-line only: control
never returns to an earlier phase.
*Obstruction (Theorem U, PROVED; audited with fixes).* Data = elements containing a variable. If the initial list satisfies
(F1) no element containing data sits directly above a closed element and (F2) no S-headed subterm has a data spine
argument directly followed by a closed one (e.g. ch(t) ++ [z1, …, zn] with t closed), then every later list of the head
run does (the run never opens a variable-headed element before it stops). Audit 6 counterexamples show the initial
condition is needed (SSxS; [Sx, S, S]). Consequences (exact): compounds formed when data are opened join two data
elements; a clean write c0·t (closed onto data) happens only when a closed element is opened with c0, t directly below it,
so t is the topmost datum; no data·closed append ever forms, and no head-style subterm with a data predecessor exists. Lemma U3 (blocking): once two y-but-not-x elements sit above the topmost
x-element, no x-element reaches the front until a y-element is opened. Checked on 408,690 random steps (0 violations).
*Generation bound: HEURISTIC only (audit 6: key notions undefined), and its slogan "nest counters cannot alternate
unboundedly" is FALSE:* the single head run of t z z for t = S(S(SS))(S(SS))(SS)S (the E36 term) follows its infinite
leftmost path (Lemma P descent, checked through E_0 … E_24); its second spine slot is an SS-nest counting down from n − 2
to 0 and then reloaded from the third slot, which gains one SS layer per cycle — unbounded alternation inside ONE head
run. So loops are possible in head runs; what has not been built is a loop that also transfers between counters.
*Also (route b, empirical):* all 892 hnf-free terms ≤ 10 leaves have unboundedly growing head-run stacks (834 linear,
58 slightly superlinear) — divergence always nests deeper; no run settles into one endless tail chain.

## Disprover round (2026-10-26): Theorem U survives zero tests; no writing behind a live control — PROVED (elementary; audit 7: correct, fixes applied)
*Setting.* A closed head run. Mark some subterm occurrences of the initial term (e.g. the bases of counters; marks may be
nested). Data = elements containing a residual of a marked occurrence (copies of c carry the marks). Opening a front
element consumes EVERY mark on its left spine and exposes its full spine: this is a *zero test* (the counter base is
executed as code). F1 = the list is closed-prefix ++ data-suffix; F2 = the FULL spine of every subterm occurrence (marks
on the left spine looked through, including inside marked terms) is closed-prefix ++ data-suffix. (Audit 7: the
full-spine form is necessary — K = [m S, M_y S, M_y S] with m = M_x(S S (M_y S)) satisfies F2 on spines that treat marks as
opaque, fails full-spine F2, and violates F1 after one step.)
*Theorem U\* (Theorem U survives zero tests).* If the initial list satisfies F1/F2, so does every later list, forever.
*Proof.* Step [a,b,c]++R ⇒ ch(a)++[c, b·c]++R. If a is closed, ch(a) is closed; by F1 either b, c are both closed (then
b·c is closed), or b is closed and c data (b·c is data, with spine closed ++ [c]), or both are data; in every case
[c, b·c] ++ R is closed-prefix ++ data-suffix and the new spine of b·c keeps F2 (if b's spine contains data, b is data, so c
is data by F1). If a is data, F1 makes b, c and R data; ch(a) — a's full spine — is closed-prefix ++ data-suffix by F2; and b·c is data·data. ∎
*Corollary W (no writing behind a live control).* Suppose moreover two tags x, y satisfy J1/J2 of Lemma 10 initially (no
element containing y lies above an element containing x but not y, in the list and in every FULL spine). Then J1/J2 hold
forever (Lemma 10's case analysis plus one case: a zero test can expose an x-only argument, but full-spine J2 puts no
y-element above it), and a clean
write — a step with b closed and c containing y — happens only when NO list element contains x without y.
*Proof.* F1 with b closed forces a closed, so c is the topmost datum; by J1 no element below c contains x without y. ∎
*Reading.* In fuel-free designs (F1/F2), while the control counter x still has a clean list element, nothing can be written
cleanly into the target y: every transfer pass must first absorb the whole live control into y-containing elements
(entangled designs) and release it later. Agent U's clean transfer R1 uses an F1 violation ("fuel": a closed constant
directly below a datum) built into the closed program P_k, which F1/F2 runs never create (Theorem U\*).
*Fuel is not conserved once present (COMPUTATIONALLY CERTIFIED example).* One F1 violation can multiply: in
[a, b, c, R1] with a data (last child data), b data and c, R1 closed, the step gives [..., last(ch a), c, b·c, R1], two
data→closed boundaries instead of one (the closed run below b is split by the new compound). Concrete run: from
[S(Sz), SSz, S(S(SS)S), SS(S(S(SS)S)), S(SSS), SS] the head-style depth of z rises from 1 to 2 in two steps
(code/hsdepth.py; random configurations: 339 of 2,432 runs raise it). So an obstruction to looping transfers cannot be a
plain fuel-conservation law; it would have to quantify fuel and handle copies.
*Checks.* code/corw_check.py (random exact runs; after audit 7 with full-spine checks and nested marks): 4,000 F1/F2 runs,
352,238 steps, 81,129 zero tests, 0 violations of Theorem U\*; 2,164 of them also J1/J2: 173,442 steps, 12,387 clean writes
onto y-elements, 0 writes while an x-only element existed, 0 violations of J. Audit 7 (independent scripts, nested marks
also on left spines): 6,000 runs / 698,502 steps / 122,861 zero tests and 6,000 runs / 695,058 steps / 30,256 writes,
0 violations.
*Agent U, rung (1) round 1 (PROVER_LOG.md entries 1–3; audit 7).* (i) Sawtooth rules — PROVED (symbolic, all values;
audit 7: correct, re-derived; 593 template hits in 3,000 concrete steps, 0 mismatches): for u(i,k) = N_i N_k S over an
opaque tape, (i≥1,k≥1) → (i−1,k) in 5 steps, (i≥1,k=0) → (i−1,0) in 7, (0,k) → (k,k+1) in 6 — the loop
{while A > 0: A−−; A := B + 1; B := B + 1}. (ii) *Frame lemma* — PROVED in the fixed form of audit 7: let the core be a
marked occurrence (A's predecessor) and its copies; take the list right after A's opening (including the compound b·c of
that step) as 'original'; then until an element containing a copy of the core reaches the front, every element below the
topmost core-containing element is an original element (unchanged) or contains the core (proof by the position p of the
topmost core-containing element: p = 1, c moves above and b·c holds the core; p = 2, b·c holds the core; p ≥ 3, nothing
below changes; random check 30,000 trials / 4,319,273 steps, 0 violations; the looser reading 'while the core is off the
front's left spine' has 1,307 counterexamples). The consequence 'the next node's arguments are old arguments or
core-compounds' needs in addition that the first core-containing front element is core-headed (true in the sawtooth).
(iii) Tape claims: one new node b·c per step (trivial); after a clean write the old copy sits directly above the new value,
so no two consecutive clean writes onto the new value (positional, audit 7: 2,609 writes, 0 consecutive); a clean write
while a data element is opened is exactly an F1 violation; 'fuel is never created' holds only for a fuel-free active
prefix whose tail is never read or is fuel-free too (FALSE otherwise: 900 of 4,985 runs with one initial F1 violation
increase the violation count); Φ's list [P_k, S, M_{m0}] with M_{m0} marked satisfies F1/F2, hence at P = 0 and forever
(Theorem U\*; checked on Φ(0,0), Φ(3,2), Φ(12,7)). Bounded searches (324 + 4,347 + 497 families): no A−−/B++ pass.
*Agent U, round 2 (PROVER_LOG.md round-2 entries; audit 8 pending for its PROVED claims).* New exact engine for counters with
arbitrary layer contexts (code/agent_u_ctxnest.py). Exactly three A−−/B++ passes were found, each 2 head steps,
(i,k) → (i−1,k+1) with B_{k+1} = S·B_k: A_i = S(S(A_{i−1}S)) (front A_i·S, tape [junk, B]); A_i = S(S A_{i−1} S) (tape
[S, B]); A_i = S(S A_{i−1})S (tape [junk, B]); a two-family scan (contexts ≤ 4 leaves on both sides) gives 140 recurrences,
all with B unchanged except two of these three. In all of them A's layer carries a closed constant right after its
predecessor (fuel w.r.t. A), as Corollary W requires; when A reaches 0 only B's data are live and the list is F1/F2, so by
Theorem U\* no B-datum is ever followed by a closed argument and A cannot be rebuilt in fuel-carrying form from B: the
loop cannot be re-entered (audit 8: the three pass rules CORRECT for all i ≥ 1, k ≥ 0, template recurring each pass;
the reload obstruction CORRECT WITH FIXES — PROVED only in the form 'A cannot be rebuilt HEAD-STYLE from B-data', and only
when the original tail is fuel-free w.r.t. B or never read; U* does not exclude rebuilding A from closed program
material or a wrapper-style A built from B, so 'no clean transfer loop' rests on the bounded scans). Scans of fuel-splitting designs (44 + 6,048 + 18 + 98 + 155
template families), entangled node templates (frame-lemma corollary: the head changes identity only at its zero test) and
Fibonacci self-compound reload sources (bases ≤ 6 leaves, 400 steps): no loop. (Audit 8 on the entangled-node
corollary: 'A head ⇒ B unchanged' true but B usually leaves the node for the tape and may be combined with stale copies;
'the head changes identity only at its zero test' is a GAP — it restates the core-headed hypothesis, which fails in
8,774 of 14,769 random templates; it must be proved per template.) Still open: fuel flowing from A into B
during the transfer (B absorbing closed constants from below it), entangled tape designs with a uniformly inert stale
part, readers for Fibonacci words.

## Geometry of head runs: the access lemma and Lemma G1 — PROVED (elementary; audit 8: G1 correct, consequence corrected; audit 9: access lemma correct, positions 1-based)
*Access lemma.* In a step [a,b,c]++R ⇒ ch(a)++[c, b·c]++R an element that was at position ≥ 3 is at position 1 or 2
afterwards only if it is c and |ch(a)| ≤ 1; then b·c, which contains a second copy of it, sits directly below it.
*Proof.* R lands at positions ≥ |ch(a)| + 3 ≥ 3; c lands at |ch(a)| + 1 with b·c right below. ∎
So a stored element (a counter waiting below the active window) re-enters positions 1–2 only by being copied, unless it
is released as a spine argument of an opened container — and a container got it by absorbing it at position 3, i.e.
again with a copy left behind. Every re-access of a stored counter therefore creates a stale copy: the geometric root of
all junk in transfer designs (agent U's 'old copy in front', Lemma 10's duplicate).
*Lemma G1 (region below the lowest y-element).* For a tag y let T(t) be the list elements strictly below the lowest
y-containing list element. If that element is not at the front during steps t0…t1, then T(t1) is a suffix of T(t0):
elements leave T only from its top, by being absorbed into the lowest y-element (their copy goes above it).
*Proof.* By the position p of the lowest y-element: p = 2 — it absorbs c, the top of T, and c's copy lands above b·c;
p = 3 — the new lowest y-element is b·c at |ch(a)| + 2 and T = R; p ≥ 4 — nothing below it changes. ∎
*Consequence (corrected by audit 8).* While the lowest y-element is not opened, at most |T(t0)| elements OF T(t0) are
absorbed, and T grows only at an opening of the lowest y-element (by its trailing non-y arguments and the recombination
[c, b·c] of T's top two elements). Closed constants lying BETWEEN y-elements are not covered and can be replenished
whenever a non-lowest y-element is opened (minimal example [S, y, S, y] → [S, y·S, y]; audit 8: 2,058 random phases exceed
|T(t0)|). Audit 8: the lemma itself CORRECT (40,000 trials, 0 violations).
*Checks.* code/geom_check.py 6000 150 5 (random runs, elements tracked by identity): 273,888 access cases, 240,328 G1
cases, 0 violations.

## The pump loop: a nested transfer loop inside one head run (agent U, round 3, 2026-10-26) — PROVED (audit 9: correct; its descent consequence REFUTED)
*Pass rule.* [S, T, S] ++ R → [S, T·S] ++ R in one step, for all terms T, R: a run of n leaves S directly below a target
T is a unary counter A, and each pass is one A−− (the supply loses an S) and one B++ (T's spine gains an S).
*Round rule (marker M = SS).* [S, X, S^n, SS, SS, R] →^{n+4} ch(X) ++ [S^n, SS, SS, R, (SS·(X·S^n·SS·SS))·R] for all n and
all X, R (induction on the pass rule plus four marker steps): the marker ends A's countdown (data-driven zero test), the
target is re-opened ('spilled') and its absorbed S's are pushed back as a fresh supply below the last spine argument of X.
*Loop.* With X = N_k (SS-nests over S(SS)(SS)), ch(N_k) = [S, N_{k−1}], so T(k, n) = [S, N_k, S^n, SS, SS, R] ↦ T(k−1, n):
control returns to the pump k times, each round making n clean A−−/B++ passes; at k = 0 the base ends the loop. Checked
concretely for k, n ≤ 5 (e.g. (5,5): 45 steps). It is the first loop with transfers and two levels of data-driven zero
tests inside one head run — but it runs only k rounds.
*Placement lemma (PROVED).* Opening a over (d2, d3) gives ch(a) ++ [d3, d2·d3] ++ R: everything released from a lies
above d3 and d2·d3. Hence closed material released by a control can lie directly below a target only if the target is an
earlier spine argument of the same opened element, and a target built from c / b·c of the control's opening lies below
all the control's released material. (Audit 9: the pass rule, the round rule — X must be S-headed — both loop variants for
all k, n by induction, and the placement lemma are CORRECT; but the claimed consequence 'in any spill re-entry the next
target is a spine argument of the current target's head or its first absorbed element — a finite descent' is FALSE: the
next target can be any absorbed element, e.g. [S, S, S, S(SSS), S], where the second absorbed element S(SSS) becomes the
target; 23,476 of 59,535 random spill re-entries are of this kind.) An infinite pump needs a generator of fresh
target heads placed between target and supply; the only unbounded generator known is the sawtooth's clean write by its
closed base. Bounded searches for a reload at k = 0 (bases ≤ 6–7 leaves, markers 2–4 leaves, 500 steps; outer counter
after the markers or between target and supply): none (EXPERIMENTALLY SUPPORTED negatives).

*Round-level transfer with head-style targets (main agent, 2026-10-26; COMPUTATIONALLY CERTIFIED for k ≤ 6, n ≤ 5, exact
list prefixes after every round; follows from the round rule for all k, n).* Take the targets X_k = S S X_{k−1} S (each
layer carries one trailing closed S) over a base B0. Since ch(X_k) = [S, X_{k−1}, S], the spill returns the layer's S
to the supply: T(k, n) = [S, X_k, S^n, SS, SS, r1, …] ↦ T(k−1, n+1). So the head counter k and the supply n form two
counters with a clean round-level transfer k → n and data-driven zero tests on both (marker at n = 0 of each pass, base
at k = 0). Missing for rung (1): a RELOAD at k = 0 that rebuilds a head counter X_m (m ≥ 1) from the supply. Search
(code/pumpreload.py 8 4 600: all bases ≤ 8 leaves, n ≤ 4, 600 steps): no reload except the trivial coincidence base = S,
where three absorbed S's form X_1(S) = SSSS and the next round sticks. Note the asymmetry behind this: appends (target at
position 2 absorbing position 3) never copy the target, whereas writes (target at position 3) always do — the transfer
k → n uses appends, the reverse transfer n → k needs nested growth, i.e. writes and their stale copies.

## Write-pass theorem: wrapping a value needs a control at least as large as the old value (agent U round 4; corrected form after audit 10) — PROVED
*Audit 10.* The original wording ('a pass that increases nesting so that the new value contains X as a proper subterm
needs |S·C| ≥ |X|') is FALSE: the pump's append [S, X, S, …] → [S, X·S, …] makes X a proper subterm of the new value
with the fixed control [S]. The bound holds when the increase is a WRITE (X in an argument position of the value), with
a size-invariant proof; and 'the prefix contains a stale copy of X' is not preserved — only its size is.
*Statement.* Call the value the list entry directly above the supply; when it is read at position 3, b·v becomes the
value and the moved copy of v is stale. Let μ = |S·P| for the prefix P above the value. If the value is never opened and
at some step a write b·v is made onto a value v ⊇ X, then from that step on μ ≥ |X| + 1. In particular a pass that ends
in the template C ++ [Y] ++ supply with Y having X in an argument position forces |S·C| ≥ |X| + 1, so no uniform pass
with a fixed control C can wrap unboundedly large values. If the value's top layer may be opened, the same bound holds
for its unopened predecessor p (|S·C| ≥ |p| + 1), still unbounded for uniform passes.
*Proof.* Steps not reading v do not decrease μ (Lemma 1 for the prefix's own step). An append (v at position 2 absorbing
s) gives μ′ = |a| + |s| ≥ μ. A write onto v (v at position 3) gives μ′ = |a| + |v| ≥ |v| + 1, since v's copy goes above
the new value. ∎ (Audit 10 searches: fixed controls of 1–3 closed terms ≤ 3 leaves, opaque value, n ≤ 3: 6 append-style
passes, 0 depth-increasing; openable layers ≤ 5 leaves: 228 same-depth passes, 0 depth-increasing.)
*Reading.* Appends (flat growth, the pump) work with a fixed control; WRAPS (nested growth) do not — the stale copy's
size stays above the value. So the transfer supply → nesting, and rebuilding a growing counter by wrapping, need a
control whose size grows with the counter: a copy of the counter is re-read every pass (full re-execution, the frontier
Theorem O left for leftmost paths).
*Stale-residue lemma (PROVED for closed values; audit 10: 14,792 write steps, 0 violations).* After a write the list is
P ++ [Y] ++ R with P containing the stale copy; if |P| ≥ 3 the run of S·P either diverges or reaches an hnf h with
|S·h| ≥ |S·P| ≥ |X| + 1 and continues from h ++ [Y] ++ R; if |P| ≤ 2 the lemma is vacuous (the next step reads Y). A
uniform repeat by executing the stale copy would need h = [S, V] of fixed size — impossible for unbounded values.
*Also (agent U round 4; audit 10: CORRECT).* A sawtooth generator N_K placed between or after the pump's markers is carried exactly
(T(i,K,n) ↦ T(i−1,K,n), symbolic) but never promoted to the next target; placed before or after the supply it destroys
the recurrence. Exact symbolic traces of write + stale execution for layers S S x S, S S x (SS), S(S x)S (22 steps) and a
concrete follow-up (k, n ≤ 4, 4,000 steps): the counter structure is destroyed, never returning to a template.
EXPERIMENTALLY SUPPORTED. Open: controls that grow with the counter (full re-execution).

## Lemma FS (prepend-only full re-execution is finite-state) — PROVED (elementary automata fact)
*Statement.* Let the state of a round-based system be a word w_r over a finite alphabet Σ (outermost symbol first), let
A = (Q, Σ, δ, q0) be a finite automaton and g: Q → Σ. If every round reads the whole current word with A and prepends the
symbol computed from the final state, w_{r+1} = g(δ*(q0, w_r))·w_r, then the sequence of prepended symbols is eventually
periodic (with preperiod and period at most |Q|^|Q|), hence every regular property of the sequence of words (w_r) is
decidable.
*Proof.* Put φ_r = δ*(·, w_r) ∈ Q^Q. Then s_r = g(φ_r(q0)) and φ_{r+1} = φ_r ∘ δ(·, s_r), so φ_{r+1} = F(φ_r) for a fixed
map F on the finite set Q^Q; the sequence (φ_r), and with it (s_r), is eventually periodic. A regular property of w_r is
decided by the state of its automaton after reading w_r, which evolves in the same way on a product automaton. ∎
*Reading.* This is the computational content of the surviving 'full re-execution' designs whose only write per round is
one global wrap of the topmost datum (Theorem C's round, the sawtooth's reload SS·N_k, Theorem J): if the full read of a
copy can influence the next write only through a bounded amount of control information, the dynamics is finite-state.
A universal design must therefore modify the INTERIOR of a word each round — e.g. a gsm pass that rebuilds the word layer
by layer while reading a copy, i.e. one write per layer read (a transfer A−−/B++ with symbols) — which is exactly the
per-pass transfer that every head-run design so far fails to sustain (FAILED_APPROACHES 24–27). Scope: the lemma assumes
the bounded-control hypothesis; designs carrying unbounded information in the control (junk, frames) are not covered.

## Full re-execution templates (agent U round 5, 2026-10-26) — no construction; bounded searches COMPUTATIONALLY CERTIFIED
Exact symbolic searches (engine code/agent_u_ctxnest.py): (i) sawtooth with a third counter in the fuel slot,
N_i·N_k·F_m (F ≤ 4 leaves, bases ≤ 3): only (i−1, k, m) [745 branches] and the reload (k, k+1, m) [731]; m never changes
although F_m is re-executed every pass (copied first, the frame keeps the old copy — frame lemma, PROVED); (ii) B from a
second family, N_i·X·c (X contexts ≤ 4 leaves, c ∈ {S, SS}): only countdowns, B never changes, no reload (A := B needs one
family); (iii) three slots N_i·N_y·N_z with reload bases ≤ 8 leaves: reloads (y, y+1, z), (y−1, y+1, z), (y, y+2, z), and
for the base S(S(SS)(SS))(SS) (y, y+1, y+1) — z is kept or overwritten by a copy, never decremented or transferred;
(iv) controls F[N_k] (F ≤ 5 leaves) over [M_m, c] or [c, M_m]: no recurrence within 60 steps. Reading (ARGUED; backed by
the searches): at A = 0 the closed base can write only onto the topmost counter (U(b) — but the sawtooth's recycled fuel
violates F1, so this is not a theorem here); a second counter that changes once per outer cycle in step with the first
would have to be opened below the topmost counter, forcing 'data holding data' with a stale copy (Lemma 10). Open:
larger bases/frames, and designs where the second counter sits inside B's frame and is decremented when B's copy is
executed each pass.

## Head-style countdown = transfer with multiplication (main agent, round 6, 2026-10-26) — COMPUTATIONALLY CERTIFIED (cases below); symbolic proof and audit 11 pending
*Fact.* Let X_j = S S X_{j−1} S^r (r trailing leaves S per layer) over B0 = S(SS)(SS). Hand derivation: X_i a b ↠ a b
(X_{i−1} S^r a b), so after j passes of the countdown (with body a = N_k, fuel b = S) the thunk is X_{i−j} S^{rj} a b —
every pass does A−− and C += r, where C counts the leaves S stored in the thunk. When A reaches 0 the base B0 arrives at
the front applied to [S^{r·i}, N_k, S]: the countdown's value, multiplied by r, delivered as a pump-style supply.
*Checks (exact concrete runs, X_i N_k S w1 w2 w3).* r = 1, 2, 3 and (i, k) ∈ {(2,1), (3,2), (5,2)}: the leading S's are
exactly r·i, followed by [N_k, S] (e.g. r = 3, i = 5: 69 steps, 15 S's).
*Pass rule — PROVED for all i, n (audit 11; agent U certified r = 1..3, n ≤ 4).* The front node T(i, n, k) = X_i·S^n·B·S becomes T(i−1, n+r, k) = X_{i−1}·S^{n+r}·B·S. Proof (audit 11): opening T gives [S, X_{i−1}, S^{r+n}, B, S, w2, w1·w2, …]; n + r pump passes give [S, X_{i−1}S^{n+r}, B, …]; one step brings a copy of B to the front with Z = X_{i−1}S^{n+r}·B below it; one step opens the copy, releasing [S, X_{k−1}, S^r]; r + 1 passes make X_{k−1} absorb S^{r+1}; one step brings Z·S = T(i−1, n+r, k) to the front. Exact step counts (A's and B's predecessors opaque, r = 1–4, n = 0–8): n + 2r + 5 for B = X_k (k ≥ 1); n + r + 5 for B = N_k (k ≥ 1); n + r + 7 for k = 0. (Correction: an earlier entry here said 'n + 2r + 6, independent of k' — off by one in the main agent's counting loop and wrong for k = 0 and for N-bodies.) B may be symbolic up to the split k = 0 / k ≥ 1; the copy of B that is opened becomes junk (X_{k−1}S^{r+1})·(Z·S), while the original B rides unchanged inside the new node.
*Zero test (audit 11, exact).* From X_i N_k S w1 w2 w3 the front node B0·S^{r·i}·N_k·S is reached after r + 4 + (i−1)(r+5) + r·i(i−1)/2 steps (k ≥ 1); matches all nine concrete runs (e.g. r = 3, i = 5: 69 steps).
*What it gives.* A clean per-pass transfer (no fuel deficit: the fuel S^r is carried in A's own layers, as Corollary W
requires) inside one infinite head run, with a data-driven zero test at A = 0. Missing: a reload at the base that starts
a new round (A := copy of a head-style B, or supply → next counter). Side search (code/hsreload.py, bases ≤ 7 leaves,
r = 1, both counters head-style over one base, 3,000 steps): no new round (for B0 = S(SS)(SS) the run continues past
3,000 steps without re-entering).
*Round 6 outcome (agent U; audit 11: candidate (a)'s failure PROVED for this node from the exact 5-step rule — the tape is read only at the pass's first step, (t1, t2) → (t2, t1·t2), with t1 the previous pass's J = (N_{k−1}S)·u(i−1,k); 'the supply sits in front of B' is a THEOREM for this family (ch(X_i) = [S, X_{i−1}, S^r] releases the fuel right after the predecessor); 'this blocks every reload' is only an observation: with base S and supply n ≥ 5 the run re-enters, S·S^5·X_k·S → X_1·X_k·S in 9 steps (the supply assembles X_1 = SSSS) — a degenerate, finite re-entry, outside the search bound n ≤ 2; the 'periodic [3,2,1,1]' pattern of base S depends on the tape constants).* Goal: combine the sawtooth's reload loop with a transfer gadget into a
looping counter program with transfers inside one head run. NOT achieved. (a) Sawtooth countdown + a counter on the tape:
the 5-step pass touches the tape only by the twist (t1, t2) → (t2, t1·t2) with t1 the previous pass's junk, so every tape
write is junk·data and t2 is copied unchanged (bounded search: C never changes). (b) Head-style countdown inside the
sawtooth frame: the pass rule above holds (A−−, C += r per pass), but at A = 0 the base meets [S^n, B, S] — the supply in
front of B — and no base ≤ 8 leaves re-enters a round X_a·S^p·X_b·S (symbolic, n ≤ 2; concrete 5,000-step runs for all
bases ≤ 6 leaves); base S settles into a periodic pattern (front depths 3, 2, 1, 1, no growth); a marker between supply
and B breaks the countdown (24/24 markers ≤ 4 leaves); no layer context ≤ 6 leaves puts the recycled fuel after B.
Clearing the supply by pumping it overshoots into B; running the S's as code collapses them into a comb W that wraps B
(W·B) while a copy of B runs — sawtooth-like, but it carried stale structure and turned periodic. (c) Pump + sawtooth:
blocked at the same point (rebuilding a head counter from the supply is the reverse transfer of the write-pass theorem).
(d) not attempted. Every growth found stays in a supply that is never read again.

## Frontier research, main agent alone (2026-10-26): growth search, layer census, supply monotonicity
*Template-free growth search (code/growth_search.py, code/growth_code.py; COMPUTATIONALLY CERTIFIED, bounded).* Instead
of matching a round template, runs are flagged when the deepest counter (SS-nest or head-style nest over the base,
anywhere inside the top four list entries) keeps increasing across time windows. Sanity check: the sawtooth is flagged.
Families: A, B both SS-nests, both head-style (r = 1, 2), or mixed, over every base ≤ 7 leaves (528 runs per family,
4,000 steps), and with an arbitrary closed control term C ≤ 5 leaves in front (C·A·B·S over bases ≤ 5 leaves, 4,232 runs,
2,400 steps). The ONLY growing runs are the sawtooth (base S(SS)(SS), SS-nests) behind 40 different control prefixes; the
one mixed hit is the sawtooth with a head-style counter riding along unchanged as its fuel.
*Layer census (code/layer_ops.py; COMPUTATIONALLY CERTIFIED, bounded).* For every one-hole closed context L ≤ 7 leaves
(predecessor p opaque, body an SS-nest or a head-style nest, supply n = 0..4): whenever the run reaches the next node
p·S^m·B·S, m = n + c with a constant c ∈ {0, …, 6} — a layer can add to the supply but never subtract. The only other
behaviour: zero-test layers such as S(SS)(SS[]) and S(SS)(SS([]S)), which pass for n = 0 (or with c = 1) and leave the
countdown pattern for n ≥ 1.
*Lemma SM (supply monotonicity) — PROVED (main agent; full argument below; NOT independently audited, since the user
stopped further subagent rounds).*
*Correction first.* The wording 'reaches a front element p·S^m·B·S' with B compared as a TERM is FALSE: random trials
(code/sm_check.py, 600,000 runs) give 2,246 cases with m < n, all with tiny bodies (B = S, SS, SSS) that coincide with
material built from supply leaves (e.g. L[p] = S(SS)(pS), B = S, n = 6: the front p·S·S already 'matches' with m = 0).
*Statement.* Let p be opaque, L a closed one-hole context, and B* a MARKED occurrence of a closed term B (copies carry
the mark; opening a marked element exposes its unmarked spine). If the head run of [L[p]·S^n·B*·S] ++ tape reaches,
without opening p, a front element p·S^m·B′·S with B′ a residual of B*, then m ≥ n.
*Proof.* Mark the n supply leaves σ_1..σ_n. After the first step the list is ch(L[p]) ++ [σ_1..σ_n, B*, S_f] ++ tape′.
(a) The lowest π-element chain. Let E_t be the lowest list element containing p and T_t the elements below it. E changes
only by absorbing the element below it (E·c), by being opened at the front (the new lowest π-element is its last
p-containing child), or, when E sits at position 3, by being replaced by the compound b·E placed below E's copy. The final
element F is p-headed, and p-headed elements are never opened before the end, so the chain ends in F's lineage.
(b) Lemma G1: while E_t is not at the front, T_t loses only its top element, absorbed into E_t. When E_t is opened at the
front, T_t gains E_t's arguments after its last p-containing child and its top two elements b, c become c, b·c.
(c) No recombination can touch T above or at B*. A recombination with b or c above B* puts a compound (b·c, or a
compound headed by a supply leaf) into T above B*. Compounds never become leaves, and every element of T above B* must
eventually be absorbed into the chain before B′. So F would get a non-leaf argument before B′, contradicting its form.
A recombination with b = B* gives B*·c, which is not a bare residual of B*. One with c = B* puts b·B* directly below the
copy of B*, so it would become the argument after B′ instead of S. So every opening of a chain element happens while T's
top lies below the final S.
(d) Supply leaves are never destroyed. While in T they leave only by absorption into the chain (b); the copy made at
that moment lands above the chain and may run at the front, but the residual stays as a spine argument of the chain
element. Containers in the chain release their arguments in order, back into T below their p-containing children,
when they are opened (c). A leaf in T never reaches the front: the chain element is always above it.
(e) So all n supply leaves are spine arguments of F, before B′, as leaves, and m ≥ n. ∎
*Checks.* code/sm_check2.py (B marked), 2 × 300,000 random runs (contexts ≤ 12 and ≤ 16 leaves, bodies ≤ 10 and ≤ 14
leaves, supply ≤ 6 and ≤ 8): the marked next-node form was reached 13,731 times, with 0 violations; m − n ranged
over 0..5.
*Reading.* Within countdown rounds the supply is monotone, the body is unchanged (frame lemma), and zero tests on the
supply can only report whether anything has been added so far. A round therefore computes a monotone, additive function
of A's layer word; subtraction can happen only at the base (e.g. base S consumes 5 supply leaves to rebuild X_1, audit
11). Every growing loop found is the sawtooth. Open: bases whose code turns a supply into a growing head counter (the
write-pass theorem requires a control carrying a copy of the value), and designs outside the countdown framework.
*Flat iterator (main agent; COMPUTATIONALLY CERTIFIED for n ≤ 11, bodies N_k and X_k, k ≤ 3).* A run of leaves is itself
a countdown: the front node S·S^n·B·S becomes S·S^{n−2}·B·S for every n ≥ 2 (n + 3 steps for SS-nest bodies, n + 4 for
head-style bodies), executing B's top layer once per pass; at n = 0 or 1 it exits, and then B is executed with the tape
as its arguments. With base S, a head-style counter X_i (X_0 = S) therefore runs: transfer r·i into the supply, count the
supply down by 2, exit on the parity — a ×r followed by a mod-2 test. (Audit 11's 'base S re-enters for n ≥ 5' is this rule:
X_1 over base S is SSSS, so X_1·S^{n−5}·B·S = S·S^{n−2}·B·S.)
*Further bounded negatives.* Growth detection with closed tapes (pool ≤ 4 leaves, tapes cccc and cdcd, bases S and
S(SS)(SS), head-style A and B, 2,400 steps; code/growth_tape.py): 324 runs, none growing. Two supplies separated by a
marker, S·S^n·M·S^m·B·S (M ≤ 6 leaves, n ≤ 6, m ≤ 3; code/two_supply.py): no marker gives a recurring two-supply node, so
no flat-to-flat transfer (which would give division by 2 with remainder) in that range.

## Synthesis of the frontier research: the counter operations found in head runs, and why they cannot compute (2026-10-26, main agent)
*Catalogue of operations found (each COMPUTATIONALLY CERTIFIED or PROVED as cited above).*
 (O1) nest countdown without side effect (SS-nests: sawtooth pass); the body is executed but unchanged (frame lemma);
 (O2) nest countdown with transfer into a flat supply, ×r (head-style layers S S x S^r; pass rule PROVED, audit 11);
 (O3) flat countdown by 2 with a parity exit (comb iterator S·S^n·B·S → S·S^{n−2}·B·S); packing a supply into one comb
      (a pump with target S) and unpacking it (opening the comb) — so flat values can be copied;
 (O4) affine copy-reload of nests at a zero test (sawtooth: A := B + 1, B := B + 1; one wrap per reload, as the
      write-pass theorem allows);
 (O5) zero tests on a supply that can only report 'nothing added yet' (supplies are monotone within a round: Lemma SM).
*Missing — and the two operations a universal design would need.* (M1) rebuilding a nest counter from a flat value
(supply → nesting): excluded for fixed controls by the write-pass theorem (audit 10); (M2) moving units from one flat
value into another (division with a kept quotient): none for markers ≤ 6 leaves (E49). Consequently ×r can be applied to
a value at most once (nest → flat), and flat values can only be counted down, copied, or parity-tested.
*Proposition MM (copy/reset/increment machines with residue tests are finite-state) — PROVED (elementary).* Let a
machine have finite control Q and counters x_1..x_k whose only updates are x_i := x_j + c, x_i := 0 and x_i := x_i + c
(c constants ≥ 0), plus temporary sums C = Σ r_j x_{i_j} that are only tested for C mod 2 (or any fixed modulus) and for
C ≤ T, then discarded; let branches depend only on such tests and on x_i ≤ T. Then for m = the lcm of all moduli and T
the largest threshold, the abstract state (q, x mod m, min(x, T + max c)) evolves deterministically on a finite set, so
the control sequence and every test outcome are eventually periodic; hence every regular property of configurations
that encode the x_i in unary (a finite automaton only sees a unary value up to a threshold and modulo a period) is
decidable along the run.
*Proof.* Each update commutes with reduction mod m and with truncation at T + max c (copies and constants act
coordinatewise; resets are constant), and each test is a function of the abstract state; a deterministic system on a
finite set is eventually periodic. ∎ (Lemma FS is the special case k = 1 with prepend-only words.)
*Conjecture R′ (operation completeness for leftmost-outermost head runs) — REFUTED (E54, 2026-10-26: the 10-leaf term SSS(SS)S(SS(SS)) has a head run that is a binary counter — gaps 15 + 6·v2(k+4), the ruler sequence — which no machine of Proposition MM can produce). Kept for the record:* After a finite transient, the
counter dynamics of every infinite head run is generated by operations of the kinds O1–O5 (with finitely many layer
shapes and bases). Evidence: the census of all 4,092 hnf-free terms ≤ 11 leaves (E47: only periodic, single linear and
two-level nested counters), the template-free growth searches (E48: only the sawtooth grows), the layer census (no
decrements), the two-supply negative (E49), the audited obstructions (U*, Corollary W, frame lemma, write-pass
theorem), and Wolfram's own exponential S-expressions S(SS)SSSS and SSS(SS)SS (NKS notes), whose leftmost-outermost
evolution ends in a 15-leaf hnf-free component whose head run is a single linear counter (E52). R′ + Proposition MM would give: no universal emulation through leftmost-outermost evaluation with a regular
detector (for hnf-free terms) — still only one evaluation order, and R′ itself is the open core.
*Flat → nest rebuild search (code/rebuild_search.py 6 1500; bounded).* Lists [C, W_n, Z, S, w1, w2] with closed control C ≤ 6
leaves, a comb W_n holding n ∈ {4, 6, 8} units and a seed nest Z (X_1 or N_1 over S(SS)(SS)): 384 runs; 9 runs grow a
nest, all of them the sawtooth mechanism (controls S(SS)(SS), S(S(SS))(SS), S(SSS)(SS)) with the same growth for every n
while the comb loses a fixed 2–7 units at the start and then stays constant — no flow of units from the comb into the
nest. The loophole of the write-pass theorem (a control carrying a copy of the value) remains unrealised in this range.
*Lemma NT (no transfer into a second supply, strict node form) — PROVED (main agent; not independently audited).* Let
M* and B* be marked occurrences, and suppose the run of [S·S^n·M*·S^m·B*·S] ++ tape reaches a front element
S·S^{n′}·M′·S^{m′}·B′·S, where M′ and B′ are BARE residuals of M* and B*. Then the m′ leaves between M′ and B′ are exactly
the original m supply leaves, so m′ = m.
*Proof.* The final form needs a bare residual of M*. So M* was never absorbed into anything below it: an absorption
M*·c leaves no bare residual below the first supply. M* was never opened: that removes the mark, and a later bare copy
would have to be a copy made at position 3, which leaves b·M* between the copy and the second supply, where the final
form forbids it. And M* was never copied at all, by the same reason. So M* stays the lowest M-element and is never at
the front. By Lemma G1 the region below M* then only loses its top element, by absorption into M*, which is again
forbidden. So that region, which includes the m leaves and B*, is untouched until the final node absorbs it. ∎
*Scope.* This covers the strict two-supply node only; it does not rule out division realised in another representation.
Together with the bounded search E49 (no recurring two-supply node at all for markers ≤ 6 leaves), the second missing
operation (M2) is absent in the forms tried.

## Binary counters inside head runs; Conjecture R′ refuted; revised Conjecture R″ (main agent, 2026-10-26)
*Observation — EXPERIMENTALLY SUPPORTED (E54).* The head run of SSS(SS)S(SS(SS)) (10 leaves; also S(SS)SSS(SS(SS)),
SSS(S(SS)S)(SS(SS)) and at least four random hnf-free terms with 15–22 leaves) is a binary counter: the gaps between
occurrences of opcode 2 alternate 9 with 15 + 6·v2(k+4) (the ruler sequence; 21 exceptions in entries 200–2,200 over
150,000 steps; value frequencies halving: 2,348, 1,172, 584, 290, 143). At every recurrence of the top pattern
[S, S(SS(SS)), S(S(SS)S)(SS(SS)), …] the list is that constant prefix, a block of 3–9 new elements, then the previous
block minus its first element; older blocks are never read again. So the counter's digits live inside the structure of
the new elements (they recur as building blocks), not in the buried list. The exact carry rule is NOT yet derived.
*Consequences.* (1) Conjecture R′ is false: the ruler sequence is not piecewise-affine in any period, so no machine of
Proposition MM produces it; head runs can modify the interior of a structure by carry propagation. (2) This is still not
universality: a binary counter is 2-automatic. (3) Revised working conjecture — *Conjecture R″ (CONJECTURAL)*: the opcode
sequence (indeed the configuration sequence, suitably encoded) of every infinite head run is morphic; MSO properties of
morphic words are decidable (Carton–Thomas), which would still give decidability of regular-pattern reachability along
leftmost-outermost evaluation of hnf-free terms. Evidence: all 4,092 hnf-free terms ≤ 11 leaves and a random sample of 1,500
with 15–22 leaves are periodic, single linear counters, two-level nested counters or binary counters — all morphic.
(4) For the universality side this is the first mechanism found that rewrites the inside of a stored structure; whether its
carry rule can be generalised to other finite-state transductions (iterated transductions can be universal) is the
natural next question.
*Mechanism (interpretation, EXPERIMENTALLY SUPPORTED, not derived).* Over 1,271 recurrences of the top pattern (20,000
steps), the size of the first new element falls steadily between long gaps (e.g. 533, 475, 383, 325, 250, 192) and jumps up
exactly at the high-level carries (gaps 26–28: to 1,251, then down to 777, then 1,249 …). This is the signature of a
Hanoi-type recursion T(j) = T(j−1), event, T(j−1) — the ruler sequence is the return depth of a depth-first traversal of a
complete binary tree — which S produces naturally, since S x y z → x z (y z) duplicates z. If confirmed, the 'binary
counter' is a depth-first traversal of a self-generated binary recursion, not stored digits; it is morphic (the ruler
sequence is a fixed point of a substitution), as Conjecture R″ requires.

## The binary counter, exact (main agent, 2026-10-26)
*Levels.* With b = S(SS(SS)), c = S(S(SS)S)(SS(SS)), W = SS, V = SS(SS) and L0 = S S b c (the packed prefix [S, b, c]), put
P_0 = S·L0, R_m = S·(S S W P_m), U_m = S S P_m R_m, P_{m+1} = S·U_m. Each P_{m+1} contains P_m twice (directly and in R_m).
*Call lemma — PROVED (induction; every piece checked symbolically with x, y, r opaque, code/sym_levels.py, and
concretely for j ≤ 8).* For every j ≥ 0 and arbitrary x, y and tape r, the head run of [P_j, x, y | r] reaches after
exactly T_j = 2^{j+4} − 8 steps a list whose first three elements are x·y, V·(x·y), ((x·y)·(S·(x·y)))·(V·(x·y)) — the
same for every j — and it inspects neither x, y nor r before that moment.
*Proof.* Base: [P_0, x, y | r] opens P_0 to L0, L0 to the prefix [S, b, c], and the prefix's six-step pass executes
x·y with the stated arguments (8 steps). Step (j ≥ 1): (1) opening P_j and its parts takes 6 steps to
[P_{j−1}, W·P_{j−1}, K_j, (x·y)·K_j, y·(x·y) | r] with K_j = (P_{j−1}·R_{j−1})·(x·y) (symbolic, all j); (2) by induction
the call P_{j−1}(W·P_{j−1}, K_j) runs T_{j−1} steps, never reading below its arguments, and then executes
(W·P_{j−1})·K_j = S S P_{j−1} K_j; (3) exactly 8 further steps (S-step, opening K_j, U_{j−2}, R_{j−2}, S S W P_{j−2},
S-step) give a list whose top four elements equal those after step (1) of a fresh call P_{j−1}(x, y) — the continuation
K_j re-enters level j−1 with the original arguments; (4) by induction that call finishes in T_{j−1} − 6 steps, again
without reading below. So T_j = 6 + T_{j−1} + 8 + T_{j−1} − 6 = 2T_{j−1} + 8, i.e. T_j = 2^{j+4} − 8. ∎
Values checked concretely: T_0..T_8 = 8, 24, 56, 120, 248, 504, 1016, 2040, 4088 (code: inline run in this session).
*Correction (2026-10-26).* The closed form is T_j = 2^{j+4} − 8 (an earlier version of this section printed 2^{j+3} − 8;
the listed values 8, 24, 56, … were right).

*Continuation lemma — PROVED.* For m ≥ 1, any term Z and any rest of the list: a list whose first three elements are
P_{m−1}, W·P_{m−1}, (P_{m−1}·R_{m−1})·Z reaches after exactly T_m − 6 steps a list whose first three elements are
Z, V·Z, (Z·(S·Z))·(V·Z); Z and the elements below the first three are never opened, and the opcode word of these steps
is u_m := w_m without its first six letters, the same for every Z and every rest.
*Proof.* The three elements are the first three after step (1) of a call P_m(x, y) with x·y = Z (step (1) is symbolic for
m ≥ 1). In that call the elements below them, (x·y)·K_m and y·(x·y), and the tape have opaque heads or are opaque, so by
the call lemma none of them, and no element with x or y at its head, is ever at the front. An element that is never at the
front can be replaced by any other term without changing which shapes are opened (opcodes are spine lengths, and such an
element never lies on the spine of an opened front), and the final three terms do not contain the replaced elements.
So the remaining T_m − 6 steps are the same for every Z and every content below the first three. ∎

*Call words — PROVED.* Let w_m be the opcode word of the call [P_m, x, y | r] (T_m letters) and A = 1 3 0 1 3 0,
B = 3 0 3 3 0 1 3 0. Then w_0 = 1 3 0 2 2 1 0 1, w_1 = A·1 3 0 2 2 1 0 1 3 0 3 3 0 2 2 1 0 1, and for every m ≥ 2
    w_m = A · w_{m−1} · B · u_{m−1},   equivalently  u_m = A·u_{m−1}·B·u_{m−1}  (m ≥ 2),  w_m = A·u_m  (m ≥ 1).
*Proof.* code/call_step_check.py re-derives the inductive step with level tokens for every j ≥ 2: from [P_j, x, y | ?]
(x, y opaque atoms, unknown rest) the head steps open shapes with opcodes A, then the call lemma at level j − 1 applies,
then 8 head steps with opcodes B, then the continuation lemma at level j − 1, which ends at the call lemma's goal; macros
are used only at level j − 1 and the unknown rest never reaches the first three. Base cases j = 0, 1 are concrete runs
with atoms (same script: correct top three after T_0 = 8 and T_1 = 24 steps, no atom opened, and the 6-step state of a
level-1 call has the continuation form). Concrete check of the recursion for m ≤ 12: code/driver_words.py. ∎

*Driver theorem (Theorem BC) — PROVED.* Write C1(k) for the three elements P_k, Q_k, P_k·(S·P_k)·Q_k (Q_k = S S W P_k).
For every k ≥ 1, a list whose first three elements are C1(k) reaches after exactly 144·2^k − 48 steps a list whose first
three elements are C1(k+1); nothing below the first three is used. The head run of SSS(SS)S(SS(SS)) has C1(2) on top at
step 376 (direct computation). Hence it has C1(k) on top at step t_k = 144·2^k − 48k − 104 for every k ≥ 2, and the run
is infinite: SSS(SS)S(SS(SS)) has no head normal form, hence no normal form.
*Proof.* code/driver_proof.py derives one cycle with the level k symbolic (valid for every k ≥ 1; the derivation fails
only if k = 0 is allowed). Folding S·U_m to the token P_{m+1} (the definition of P_{m+1}), the cycle is 26 head steps and
seven macro steps (call lemma = CALL, continuation lemma = RESUME), in this order (numbers are the opcodes of the
explicit head steps):
    [CALL k] 4 0 [CALL k] 3 0 3 3 0 1 3 0 [RESUME k] 3 0 [CALL k] 3 0 5 0 [CALL k] 3 0 1 3 0 [RESUME k+1] 5 0 1 3 0 [RESUME k+1]
with call arguments (Q_k, P_k(S P_k)Q_k), (W·P_k, P_k(S P_k)Q_k), (W·P_k, Q_k R_k (S S W Q_k)), (W·P_k, R_k) and resumed
products Z = Q_k, U_k P_{k+1} (S S W U_k), P_{k+1}. After each macro the rest of the list is treated as unknown, and the
derivation checks that it never reaches the first three. Length: 26 + 4T_k + (T_k − 6) + 2(T_{k+1} − 6) = 144·2^k − 48.
Concrete check: C1(k) is on top exactly at t_k for k = 2, …, 12, up to step 589,144 (code/driver_check.py). ∎

*Corollary (the opcode word is morphic) — PROVED.* The opcode sequence of the head run of SSS(SS)S(SS(SS)) is
X = τ(σ^ω(h)), where σ fixes the letters 0–5,
    σ(u) = 1 3 0 1 3 0 u 3 0 3 3 0 1 3 0 u   (= A u B u),      σ(h) = h·D,
    D = A u 4 0 A u B u 3 0 A u 3 0 5 0 A u 3 0 1 3 0 A u B u 5 0 1 3 0 A u B u   (A, B written out as letters),
and τ fixes 0–5, τ(h) = the first 376 opcodes, τ(u) = u_2 (50 letters). Indeed σ^n(h) = h·D(u)·D(σu)···D(σ^{n−1}u)
and τ(σ^i u) = u_{2+i}, so τ(D(σ^{k−2}u)) is the cycle from C1(k) to C1(k+1). σ^ω(h) is a pure morphic word, and a
non-erasing image of one is morphic. Concrete check: the predicted word equals the real opcode word on all 589,144
steps (code/driver_words.py). So Conjecture R″ holds for this term. The observed ruler law 15 + 6·v2(k+4) is a
consequence (each level descended costs the 6 letters of A); the 21 incomplete trees of the earlier tree parse are
superseded by this exact description.

*What this does and does not give.* It is a complete, exact account of one infinite head run, of a kind (binary counter)
that refuted Conjecture R′. It says nothing about other terms, other evaluation orders, or universality, and it is not
a step that the prize rules count by itself.

*The five binary counters of E54 are this one machine (COMPUTATIONALLY CERTIFIED); the 12-leaf census (E56) shows that binary counting also occurs through other machines (only 21 of its 111 binary-counter endpoints are this one).* The
head runs of S(SS)SSS(SS(SS)), SSS(S(SS)S)(SS(SS)), SSS(SSS(SS)S(SS(SS)))(S(S(SS)(SS))S) and SS(SS)SS(SS(SSS)(SS)S)(SS(SS))
have C1(k) on top at t_k + δ with δ = +1, −2, +2, +8 (k = 0..7 checked, code/same_counter.py); by Theorem BC each is the
same infinite binary counter from C1(1) on (and has no normal form). Also t_0 = 40, t_1 = 136 for SSS(SS)S(SS(SS)).

## Call algebra: the mechanism generalises to every fixed recursion scheme (main agent, 2026-10-26)
*Definition.* A **call** is a term C such that for all terms x, y and every tape r the head run of [C, x, y | r] brings
x·y to the front after exactly T(C) steps, never opening x, y, never opening anything below its two arguments and never
popping any element of r; the list then is [x·y, J | r] with a nonempty junk list J.
*Composition.* For k ≥ 2 and calls A_1, …, A_k put seq(A_1, …, A_k) := S·N_1 with N_i = S·A_i·N_{i+1} (i < k) and
N_k = A_k·S, i.e. S(S A_1 (S A_2 (⋯ (S A_{k−1} (A_k S))))). Call **tree calls** the terms built from SS by seq.
*Theorem CA — PROVED.* SS is a call with T = 2, and every tree call is a call with T(seq(A_1, …, A_k)) = ΣT(A_i) + k.
*Proof.* SS: [SS, x, y | r] → [S, y, x·y | r] → [x·y, y·(x·y) | r]. For C = seq(A_1..A_k), Z := x·y:
(i) [C, x, y | r] → [N_1, y, Z | r] → [A_1, N_2, Z, y·Z | r] (2 steps).
(ii) A list [A_i, N_{i+1}, Z | ρ] (ρ nonempty, i < k) is the start of the call A_i(N_{i+1}, Z): after T(A_i) steps the
front is N_{i+1}·Z with nonempty junk above the untouched ρ. If i + 1 < k, N_{i+1}·Z = S A_{i+1} N_{i+2} Z opens in one step
to [A_{i+1}, N_{i+2}, Z | ρ′] with ρ′ nonempty (the two elements it consumes as values are junk or ρ's top; nothing is
opened).
(iii) If i + 1 = k the front is (A_k·S)·Z. *Continuation lemma:* for a tree call A and any Z, v1, v2, ρ, the list
[(A·S)·Z, v1, v2 | ρ] brings Z to the front after exactly T(A) steps without opening Z, v1, v2 or ρ, and without popping
ρ. For A = SS: [S S S Z, v1, v2 | ρ] → [S, S, Z, v2, v1·v2 | ρ] → [Z, S·Z, v2, v1·v2 | ρ]. For A = seq(A′_1, …): two
steps give [A′_1, N′_2, Z, S·Z, v2, v1·v2 | ρ], which agrees in its first three elements with the 2-step state
[A′_1, N′_2, x′·y′, y′·(x′·y′) | r′] of a fresh call A(x′, y′) with x′·y′ = Z. In the fresh call the fourth element has
the opaque head y′ and is never opened, and r′ is never popped; so the remaining T(A) − 2 steps run identically, with S·Z
and [v2, v1·v2 | ρ] in their places, and bring Z to the front.
(iv) Adding up: T(C) = 2 + ΣT(A_i) (i < k) + (k − 2) + T(A_k) = ΣT(A_i) + k. At every single step in (ii) at least two
elements lie between the front and r (junk is nonempty and y·Z or its replacement stays above r), so r is never popped;
x, y are never opened because Z is never opened before it reaches the front. ∎
*Corollaries.* (a) k-ary counters: P_0 = SS, P_{m+1} = seq(P_m, …, P_m) (k copies) gives T_{m+1} = kT_m + k, i.e.
T_m = ((3k − 2)k^m − k)/(k − 1); checked concretely for k = 2..6 (code/kary_check.py), and the composition rule on 225
random mixed tree calls (code/call_algebra_check.py, 0 mismatches). (b) Mixed radix and mutual recursion (different
schemes per level, several families) are all tree calls. (c) The opcode word of a tree call is its depth-first call-tree
traversal, so it does not depend on x, y or r: a call cannot branch on data. Any data-dependent behaviour must come from
the continuation x·y and from whatever builds new levels (in the binary counter, the driver of Theorem BC).
*Search context (EXPERIMENTALLY SUPPORTED).* All one-context schemes P_{m+1} = F[P_m] with F ≤ 7 leaves over the bases SS
and S(SSbc), P_0..P_5 all calls (39,874 pairs, code/scheme_search.py, data/scheme_search_7.txt): growth laws linear (+1 to
+6), ×2 (+2, +3, +4, +5, +8, +9) and ×3 (+3, +4, +5). The ×2+8 scheme F = S(SSS(SS)H) on S(SSbc) has exactly the binary
counter's T_j = 2^{j+4} − 8.
*What this means.* The binary counter's mechanism is not special: S-calls compose into arbitrary fixed recursion schemes,
so head runs of S-terms realise at least every finite call tree. This is a positive ingredient (control structure without
any K or I) but not universality: tree calls are data-blind, and the open question remains whether a driver can build
new levels in a data-dependent way.

## S-numerals iterate calls; multiplier gadgets (main agent, 2026-10-26)
*Definition.* n̄ := (SS·)^{n−1}SS, i.e. 1̄ = SS, 2̄ = SS(SS), 3̄ = SS(SS(SS)), … (n ≥ 1).
*Theorem N — PROVED.* For every call P (in the sense of Theorem CA), n ≥ 1 and all Z, v1, v2, ρ: the list
[(n̄·P)·Z, v1, v2 | ρ] brings Z to the front after exactly 2n + (n − 1)·T(P) steps, running P as a call n − 1 times,
without opening Z, v1, v2 or ρ and without popping ρ. Consequently S(S S n̄ P) is a call with
T = n·T(P) + 2n + 3, and the levels P_{m+1} = S(S S n̄ P_m) form an n-ary counter scheme of linear size (+2n + 3 leaves
per level) — the numeral is data inside the code that sets the branching factor.
*Proof.* n = 1: (SS·P)·Z = S S P Z opens to [S, P, Z, v2, v1·v2 | ρ] → [Z, P·Z, v2, v1·v2 | ρ] (2 steps). n = m + 1:
((SS·m̄)·P)·Z = S S m̄ P Z opens to [S, m̄, P, Z, v2, v1·v2 | ρ] → [P, m̄·P, Z, v2, v1·v2 | ρ] (2 steps); P is a call, so
after T(P) steps the front is (m̄·P)·Z with nonempty junk above the untouched [v2, v1·v2 | ρ]; by induction 2m + (m−1)T(P)
further steps bring Z to the front. Total 2n + (n − 1)T(P). For the level: [S(S S n̄ P), x, y | r] → [S S n̄ P, y, Z | r]
→ [S, n̄, P, Z, y·Z | r] → [P, n̄·P, Z, y·Z | r] (3 steps, Z = x·y), then T(P) + 2n + (n − 1)T(P). ∎
Checked concretely: n = 1..10 with P = SS, S(SSbc) and a level-3 tree call — both formulas 30/30 (code/numeral_check.py).
*Gadget scan (COMPUTATIONALLY CERTIFIED for the listed G).* For P_{m+1} = S(S S G P_m), every S-term G ≤ 7 leaves over
three bases (code/gadget_scan.py): multipliers 1 (constants +5 … +13), 2 (+7 … +13), 3 (+9 … +17) and 4 (+12 … +15);
e.g. G = SSSS ×2 (+8), SSS(SS) ×3 (+10), SS(SSS(SS)) ×4 (+12). The constant does not depend on the base.
*In real head runs.* The 23-leaf term S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(SSS(SS)))) (found by code/rand_radix.py) is a
TERNARY counter: its recurring front calls are L_{m+1} = S(S S G L_m) with G = SSS(SS), sizes 24 + 8m, T = 8, 34, 112, 346,
1048, 3154, 9472 (T_{m+1} = 3T_m + 10), and its opcode-4 gaps satisfy g_{n+1} = 3g_n + 56 exactly for six consecutive
levels (141 … 123,173) (code/explore_levels.py, code/run_profile.py; EXPERIMENTALLY SUPPORTED — the driver is not
derived). So the k-ary mechanism occurs spontaneously, not only in designed schemes.
*Limits.* A call never touches its tape, so iterating a call only spends time; an iteration that changes data would need a
non-call body that reads the previous iteration's return values from its tape (the 'supply' regime of the frame and access
lemmas). Whether such bodies can be chained without the stale-copy obstruction is the open universality question.
*Remark on R″.* Two census endpoints (S(SS)S(S(S(S(SSS))S))S, S(SS)S(S(S(SS(SS))S))S) open front elements with spine
length growing without bound (≥ 50 after 200,000 steps), so a morphic statement needs a finite coding (e.g. opcodes
capped, or the run's level structure); Conjecture R″ is to be read that way.

## Order independence: what holds for every evolution order (main agent, 2026-10-26)
Wolfram's announcement leaves the evolution order open (weak definition: some path; strong: the multiway system), so a
non-universality proof must cover every order. This section separates what is order-independent from what is not.
*Standard facts used (cited, not re-proved).* (F1) S-reduction is an orthogonal (left-linear, non-overlapping) and
non-erasing term rewriting system (every variable of S x y z occurs in x z (y z)). (F2) Confluence of orthogonal systems.
(F3) Church's theorem for non-erasing orthogonal systems (O'Donnell 1977; Klop's survey 'Term Rewriting Systems' 1992;
Terese 2003, §4.8): a term that has a normal form is strongly normalising — via the conservation property: one step
cannot turn a term with an infinite reduction into one without. (F4) Waldmann ('The combinator S', Information and
Computation 159, 2000): the set of normalising S-terms is a regular tree language (normalisation is decidable).
(F5) Böhm trees of an orthogonal system are invariant under reduction: every reduct of t has the Böhm tree of t.
*Theorem T (termination is all-or-nothing and decidable) — PROVED from F1–F4.* For every S-term t exactly one holds:
(a) every reduction sequence from t is finite, and all end in the same normal form, and the multiway graph of t is finite;
(b) no reduction sequence from t ends — every maximal evolution, in every order (sequential, parallel, or any choice of
redexes), is infinite. Which case holds is decidable.
*Proof.* If t has a normal form it is strongly normalising (F3); its reduct graph is finitely branching and has no
infinite path, so it is finite (König), and confluence (F2) gives one normal form. If t has no normal form, a finite
maximal evolution would end in a normal form, contradiction. Decidability is F4. ∎
*Consequences.* (1) Any emulation whose halting signal is 'the evolution stops' (or 'the multiway graph is finite') fails
for every evolution order: halting would be decidable. (2) Every halting signal that is a property of the Böhm tree (finite
tree, no ⊥, finite leftmost/rightmost path, …) is order-independent by F5 — the finite-model results (C6, C8, P2, the path
models) apply to all orders and to the multiway system at once, to the extent that those models are proved.
*Order-dependent (leftmost-outermost / head-run results only).* Theorem U*, Corollary W, frame lemma, access lemma,
Lemma G1, placement lemma, write-pass theorem, Lemma SM, Theorem O, Theorem BC, Theorem CA, Theorem N, Proposition MM's
catalogue. None of them says anything about detectors that read intermediate states under other orders. Internal steps do
change the front element's spine (e.g. S S S x → S x (S x) inside the front element), so head-run structure is not
preserved by orders that reduce inside the front element.
*What a disproof still needs (both definitions).* For every admissible order (or the multiway system): no non-universal
detector reading intermediate states of a non-terminating evolution can carry a universal emulation. Nothing here covers
that, for any order other than leftmost-outermost, and even for leftmost-outermost only designs within the proved
hypotheses are excluded. Conversely, a universality proof may choose one order, so a single leftmost-outermost construction
would suffice.

## The ternary counter, exact (Theorem TC) (main agent, 2026-10-26)
Term: τ3 := S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS(SSS(SS)))) (23 leaves, found by random search, E57). Put G = SSS(SS),
V′ = S S G, L_0 = S(SS(S(SS)(SS(SS)(SS)))(S(S(SS)S)(SS(SSS(SS))))), L_{m+1} = S·(S S G L_m) (one copy of L_m; +8 leaves).
*Ternary call lemma — PROVED.* For every m ≥ 0, all x, y and every tape r, [L_m, x, y | r] reaches after exactly
T_m = 13·3^m − 5 steps a list whose first three elements are Z, V′·Z, (Z·(S·Z))·(V′·Z) (Z = x·y), never opening x, y
and never popping r; the first three steps (m ≥ 1) give [L_{m−1}, G·L_{m−1}, Z, y·Z | r]. *Continuation lemma* (as for
the binary counter): from any list whose first three elements are L_{m−1}, G·L_{m−1}, Z the same top three are reached
after T_m − 3 steps, for every Z and every rest. *Proof.* code/tern_proof.py derives the inductive step for every
j ≥ 2 with macros only at level j − 1: trace 1 3 0 [call j−1] 5 0 1 0 2 1 0 2 3 0 [resume j−1] 3 3 0 [resume j−1], so
T_j = 16 + T_{j−1} + 2(T_{j−1} − 3) = 3T_{j−1} + 10. Base cases m = 0, 1 and the 3-step form concrete
(code/tern_check_all.py); the continuation lemma follows from the call lemma exactly as before (the fourth element y·Z
has an opaque head, the tape is never popped). ∎
*Theorem TC — PROVED.* Let C1′(k) = [L_k, S S G L_k, L_k·(S·L_k)·(S S G L_k)]. For every k ≥ 1 a list with C1′(k) on top
reaches C1′(k+1) on top after exactly 11·T_k + 27 = 143·3^k − 28 steps (code/tern_proof.py: 9 head steps and 5 macros,
[call k] 4 0 [resume k+1] 3 3 0 [resume k] 3 0 [resume k+1] 5 0 [resume k+1]; the unknown rest never reaches the top).
The head run of τ3 has C1′(1) on top at step 167, hence C1′(k) on top at t′_k = (143·3^k − 39)/2 − 28k for every k ≥ 1;
τ3 has no normal form. Its opcode word is morphic: σ(u) = 1 3 0 u 5 0 1 0 2 1 0 2 3 0 u 3 3 0 u and σ(h) = h·D with
D = (130u) 4 0 σ(u) 3 3 0 u 3 0 σ(u) 5 0 σ(u), τ(h) = the first 167 opcodes, τ(u) = u_1. ∎
*Certified:* C1′(k) on top exactly at t′_k for k = 1..9 (to step 1,407,063); the predicted opcode word equals the real one
on all 1,407,063 steps; T_m for m ≤ 9 and the call-word recursion for m ≤ 9 (code/tern_check_all.py).
*Structure shared with Theorem BC.* Both drivers are the configuration [P, S S X P, P(S P)(S S X P)] with the gadget
X = W = SS (binary) or X = G = SSS(SS) (ternary), and both level calls return the gadget-dependent top
[Z, (S S X)·Z, (Z(SZ))((S S X)·Z)]. So the counting base is set by one small gadget inside an otherwise identical driver.

## Counters in every base (Theorem K) (main agent, 2026-10-26)
For μ ≥ 3 put X_μ = (SS·)^{μ−3} SSS(SS) (so X_3 = SSS(SS), X_4 = SS(SSS(SS)), …), V_μ = S S X_μ,
L_0 = S(S S (S(SS)) (S(S(SS)S) V_μ)), L_{m+1} = S·(S S X_μ L_m), C1(k) = [L_k, V_μ·L_k, L_k·(S·L_k)·(V_μ·L_k)].
*Theorem K — PROVED.* For every μ ≥ 3:
(i) every L_m is a call: [L_m, x, y | r] reaches after exactly T_m steps the top [Z, V_μ·Z, (Z·(S·Z))·(V_μ·Z)] (Z = x·y),
    never opening x, y, never popping r, where T_0 = 8 and T_m = μ·T_{m−1} + 2μ + 4;
(ii) for every k ≥ 1 a list with C1(k) on top reaches C1(k+1) on top after exactly 2T_k + 3T_{k+1} − 3 steps, using only
    the first three elements;
(iii) the term t_μ := S·L_1·(V_μ·L_1)·(L_1·(S·L_1)·(V_μ·L_1)) (146 + 24(μ − 3) leaves) has C1(k) on top for every k ≥ 1:
    its head run is an infinite base-μ counter, t_μ has no normal form, and its opcode word is morphic (as in Theorem TC).
Together with Theorem BC (base 2): **for every base μ ≥ 2 there is an explicit S-term whose leftmost-outermost head run is
an exact base-μ counter**, and the base is set by one numeral-like gadget inside an otherwise fixed driver.
*Proof.* μ = 3 is Theorem TC's derivation (its base differs only in the irrelevant b-part; code/kcounter_proof.py redoes
μ = 3..7 with this base). For all μ ≥ 4 at once, code/kcounter_general.py treats the gadget as an opaque symbol N, with
one extra macro, the *unroll lemma*: for μ ≥ 4 and a call L of the scheme, [(X_μ·L)·Y′, v1, v2 | ρ] reaches after
(μ − 3)(T(L) + 2) steps the top [Y, V_μ·Y, (Y(SY))(V_μ·Y)] with Y = (X_3·L)·Y′. (Induction on μ: (X_μ L)Y′ =
S S X_{μ−1} L Y′ opens to [S, X_{μ−1}, L, Y′, v2, v1·v2 | ρ] → [L, X_{μ−1}·L, Y′, …] in 2 steps (opcodes 4 0); the call L
then puts (X_{μ−1}·L)·Y′ on top with the call lemma's return values; for μ − 1 = 3 this is the claim.) With these macros
the call lemma's inductive step (every j ≥ 2, macros only at level j − 1) is
    1 3 0 [call j−1] [unroll j−1] 5 0 1 0 2 1 0 2 3 0 [resume j−1] 3 3 0 [resume j−1],
and the driver (every k ≥ 1) is [call k] 4 0 [resume k+1] 3 3 0 [resume k] 3 0 [resume k+1] 5 0 [resume k+1]; neither
ever opens N, so both hold for every μ ≥ 4. Base cases j = 0, 1 for all μ ≥ 4 at once: code/kcounter_base.py (N opaque;
level 0 in 8 steps; level 1 via [call 0], [unroll 0], with its 3-step state [L_0, N·L_0, Z, …]). The continuation lemma
follows from the call lemma as before. The step counts follow by adding macro costs (call T_m, resume T_{m} − 3,
unroll (μ − 3)(T + 2)). ∎
*Certified:* C1(k) on top at exactly the predicted steps for μ = 3..8 (5–7 levels each, runs up to 2,089,825 steps;
code/kcounter_certify.py). The derivation traces for μ = 3..7 with concrete gadgets agree with the general one
(code/kcounter_proof.py).
*Meaning.* Head runs of S-terms can count in any base, with the base written as data (a unary gadget) in the term. This is
a positive, programmable ingredient; it is still a fixed recursion (morphic, consistent with Conjecture R″) and does not
by itself give data-dependent control or universality.

*Theorem K′ (small terms) — PROVED.* For every μ ≥ 3 the term τ_μ := S(SS)SS(SS(SS)(SS))(S(S(SS)S)(SS·X_μ)) (2μ + 17
leaves; τ_3 is the 23-leaf ternary counter of Theorem TC) has an infinite head run that is an exact base-μ counter: it
reaches C1(1) of the scheme with base L_0 = S(SS (S(SS)(SS(SS)(SS))) (S(S(SS)S)(SS·X_μ))) and then every C1(k).
*Proof.* μ = 3: Theorem TC. μ ≥ 4 at once (gadget opaque, code/small_kcounter_proof.py): the base call and the level-1 call
satisfy the call lemma with this base (the b-part only changes the base's internal steps; the return top is the same), and
the head run of τ_μ reaches C1(1) using only level-0 macros, never opening the gadget; then Theorem K's inductive step
and driver apply (they are base-independent given the base cases). ∎ Concretely: C1(k) at steps 52, 167/197/227/…
(= 77 + 30μ for k = 1) and onward for μ = 3..8 (code/small_kcounters.py).
*Letters come from the base.* With levels carrying different gadgets (a word), every level is still a call with
T_{m+1} = μ(a_m)T_m + 2μ(a_m) + 4 and the base's return top (200/200 levels over 40 random words, code/word_levels.py).
But a driver started with a foreign gadget writes it once and then only the base's gadget (level words 3^k·4·3,
4^k·3·4, …, code/small_kcounters.py part (b)): new levels take their gadget from the return values, which the base fixes.
*How the driver writes the next level (read off the symbolic states, code/driver_states.py).* C1(k) is the universal
return form R(Z) := [Z, V·Z, (Z·(S·Z))·(V·Z)] with Z = L_k — the very top that every call of the scheme returns. One cycle:
the call L_k(V·L_k, Y) (Y = the third element) returns R(V·L_k·Y); V·L_k·Y = S S X L_k Y re-enters as the body of L_{k+1}
with product Y (resume k+1); Y = L_k(S L_k)(V L_k) opens to the continuation of a level-k call with product V·L_k
(resume k); its return R(V·L_k) contains S·(V·L_k) = L_{k+1} inside (Z·(S·Z)); two more resumes at level k+1 end in
R(L_{k+1}). So the driver iterates Z ↦ S·(V·Z) on the return form, and the gadget of the new level is the X inside V,
which every return re-emits from the base. (Coarse-orbit experiment, code/coarse_orbits*.py: starting R(Z) from small
terms never returns to an R-form; from terms built around the base the R-forms are all nested returns in depth-first
order, so the experiment as set up does not isolate a coarse map — inconclusive.)

## Bridge: head-run structure → the prize criterion (leftmost-outermost only) (main agent, 2026-10-26)
*Window codings.* For k ≥ 3 and d ≥ 1 let the (k, d)-window letter of a head-run step be the shapes of the first k list
elements cut at depth d (absent elements marked; a finite alphabet A_{k,d}); the (k, d)-window word of t is the sequence of
these letters along its head run, and the d-window word is the (3, d)-window word. Opcode words are images of 3-window
words under a letter-to-letter map.
*Effective Conjecture R″_{k,d}.* For every S-term t with an infinite head run, its (k, d)-window word is morphic, and
morphisms (σ, τ) with word = τ(σ^ω(a)) can be computed from t. R″_d means R″_{3,d}. (R″_{3,d} is PROVED for the terms of
Theorems BC, TC, K, K′ and for every term certified by the automatic provers; R″_{k,d} for every k for every term with a
whole-list certificate — Corollaries LP′ and CA′ — which since E69/E70 covers every proved run. Open in general.)
*Fact (Carton–Thomas, 'The monadic theory of morphic infinite words and generalizations', Information and Computation
176, 2002).* The monadic second-order theory of (ℕ, <, letter predicates) of a morphic word is decidable, uniformly in
the morphisms.
*Proposition UB (conditional) — PROVED given the hypotheses.* Assume effective R″_{k,d} for every k and d. Consider any
emulation in which (i) the encoder is computable, (ii) the evolution order is leftmost-outermost, (iii) the detector is a
finite automaton reading, at each step, only a bounded window of the state — the first k list elements to depth d — and
(iv) the emulated machine is declared halted at the first step at which the detector accepts. This covers detectors that
halt within c steps on each state written head first (S[a][b][c]…): they read at most c symbols, hence only the
(c, c)-window. *Correction (2026-10-26, later):* an earlier version assumed only R″_d (first three elements) while claiming
the bounded-time case; with tiny first elements a bounded prefix reaches further down the list, so the bounded-time case
needs R″_{k,d} for all k. With R″_{3,d} alone, UB covers detectors that read only the first three elements to bounded
depth. Then halting of the emulated machine is decidable;
hence the emulated machine is not universal. *Proof.* Given an input, compute its term t (by (i)); if t is normalising,
the run is finite and is simulated outright (Theorem T); otherwise compute (σ, τ) for the (k, d)-window word ((k, d) = the
detector's window). 'The detector accepts at some step' is expressible in MSO over the window word (the automaton's
run is an MSO-definable labelling), so it is decidable by Carton–Thomas. ∎
*What this does and does not say.* It turns the leftmost-outermost part of a disproof into one precise structural
statement, effective R″. It does not prove R″; it does not cover detectors that read unboundedly much of a state (e.g.
sizes of deep subterms), other evolution orders, or the multiway definition. Conversely, a universal leftmost-outermost
emulation of this kind would refute effective R″, so R″ is also exactly what a universality construction must break.

*Weakening the bridge (later, 2026-10-26): profinitely ultimately periodic words suffice.* Carton and Thomas define: an
infinite word α is *profinitely ultimately periodic* if it factors as α = u_0 u_1 u_2 ⋯ (finite words u_n) such that for
every morphism σ from the free monoid into a finite semigroup the sequence (σ(u_n)) is ultimately periodic; *effectively*
so if, given σ, one can compute the preperiod and period. Theorem (Carton–Thomas 2002; as stated in Berthé et al., 'The
monadic theory of toric words', arXiv:2311.04895, Thm 4.1): if α is effectively profinitely ultimately periodic, the MSO
theory of (ℕ, <, P_α) is decidable; morphic words are effectively profinitely ultimately periodic. Hence Proposition UB
holds with *Conjecture R″_PUP*: every (k, d)-window word of every head run is effectively profinitely ultimately periodic —
weaker than morphic. *Lemma PUP (nested loops) — PROVED.* Every word ∏_m E_m built by nested loops whose repetition counts
and block exponents are affine in the enclosing loop counters is effectively profinitely ultimately periodic: in a finite
semigroup g^m is ultimately periodic in m for each fixed g, and by induction on the nesting depth the image of each loop
body is ultimately periodic in the enclosing counters; images of products of finitely many such factors are then
ultimately periodic as well. This covers the linear loops (Theorem LP), the countdown words (Lemma NW, which are even
morphic) and the *square* words ∏_m (X Q^{m+c} Y)^{m+c′} Z found in E73, whose morphicity is in doubt: in a fixed point of
a polynomially growing morphism each round is a product of images σ^j(z) of increasing length, not m equal copies of a
block of length ≈ m (an argument, not a proof). So Conjecture R″ in its morphic form may be false while R″_PUP — all that
UB needs — still holds for every run seen. *Resolved (later the same day): it is false — Theorem NM.*

## Parallel evaluation as a head machine with evolving waiting elements (main agent, 2026-10-26)
*Lemma PH — PROVED (from the definition of ReplaceAll; checked on 129 passes of four terms, code/parallel_head_check.py).*
If t = S e1 e2 e3 e4 … en (n ≥ 3), one ReplaceAll pass gives P(t) = e1 e3 (e2 e3) P(e4) … P(en): the list
[e1, …, en] becomes spine(e1) ++ [e3, e2·e3, P(e4), …, P(en)]. *Proof.* The root has more than three head arguments
(n > 3) or is the redex (n = 3); a pass recurses top-down into function and argument, applies P to each argument
e4 … en, and at the node S e1 e2 e3 contracts the redex without entering e1, e2, e3. ∎
*Consequences (remarks).* (1) Under parallel evaluation the head still performs one head-machine step per pass, but every
element below the first three evolves meanwhile. (2) Code that waits is rewritten unless it is a normal form: the levels
of Theorems BC/TC/K contain redexes (e.g. U_m = S S P_m R_m), so their waiting copies decay, which is why the parallel
runs of the counter terms look nothing like their head runs (E59). The tree calls of Theorem CA are normal forms
(S·N with N = S A N′ and N_k = A·S have no S with three arguments), so they do not decay while waiting; with inert (atomic) arguments the k-ary levels
remain calls with exactly the head-machine times under parallel evaluation (k = 2, 3, levels 0–4; also 50 random mixed tree calls;
COMPUTATIONALLY CERTIFIED, E59) — a first leftmost-outermost structure that survives the change of order; a proof is open. (3) By the usual commutation of head and inner steps in orthogonal
systems, a parallel run should be the head run under a time change (head steps done early inside waiting elements) plus
inner reductions — a sketch, not checked; it would reduce the parallel case to the head run plus the evolution of
copies.

## Capability map of leftmost-outermost (head-run) programming in pure S (main agent, 2026-10-26)
*Available (PROVED):* subroutine calls closed under sequencing (Theorem CA); numeral loops — (n̄·P)·Z runs the call P
n − 1 times and continues with Z, i.e. a case analysis on n (Theorem N); head-machine booleans — [S, c1, c2 | r] runs c2
with c1·c2, [SS, c1, c2 | r] runs c1·c2 (two steps); recursion schemes of any fixed shape, including every counting base
(Theorems BC, TC, K, K′); drivers that rewrite the code they run (level k → k+1) without ever reading below the top of the
list; exact countdown/transfer passes (earlier rounds, R29).
*Observed limits (PROVED where stated, otherwise within the tested designs):*
(a) *Calls carry no data (PROVED, elementary).* After the first step of [C, x, y | r] the argument x exists only inside
x·y, so every element above r, in particular every return value, is a term over S, y and Z = x·y; since y is a subterm of
Z, a call's return values carry no information beyond Z, and its run (opcode word) does not depend on x, y, r at all.
(b) In every scheme found the return values are fixed functions of Z (BC, TC, K, SS-based levels; FAILED_APPROACHES 32).
(c) Numeral loops cannot accumulate (exhaustive to 11–12 leaves, see FAILED_APPROACHES 30; proof sketch below): the loop continuation Z is fixed for the whole loop, and opening (m̄·P)·Z only
re-enters the loop, so the numeral can be executed but not inspected or rebuilt from inside (no body ≤ 9 leaves
transforms an accumulator, FAILED_APPROACHES 30).
(d) Drivers copy the gadget of each new level from the base's return values, so the counting base cannot change from
cycle to cycle (FAILED_APPROACHES 31).
(e) The older obstruction theory (frame lemma, write-pass theorem, Theorem O, U*) already limits writes and transfers.
*The frontier, stated precisely.* Every positive mechanism found is a fixed recursion whose only data is the code it
rewrites in a fixed way. A universal leftmost-outermost emulation needs a step whose effect depends on data — some datum
opened at the front that selects between different rewrites of the code — and none of the mechanisms above provides one.
By Proposition UB this is exactly the gap between the counters and a counterexample to Conjecture R″.
*No-accumulation sketch (CONJECTURAL as a theorem; exhaustive evidence above).* In a loop iteration [P, X, Z, A, J | r]
the accumulator A starts directly below the only element containing the loop control X (namely X·Z). By Lemma G1 (tag X)
the region below the lowest X-element loses elements only by absorption into that X-element, so while A is there it can
only become an extra argument of the control (passed on unchanged). A copy of A can escape above the control only when
an X-element is merged with it as (X·Z…)·A, and then every X-element lies below the escaped copy and carries the old A;
an element built from the copy can reach a later control only as its head or after being opened again. Turning this into
a proof needs an invariant for the escaped copies; not done.
*Correction to the sketch (2026-10-26).* Transformed values CAN be created inside an iteration: e.g. if the front opens
an inserted element (S u)·(X·Z) to [u, X·Z, A, …] and u has two spine arguments [p, q] with q control-free, the next
steps give [p, q, A, …] and then the element q·A (for q = SS: the successor of A). What the exhaustive searches show is
only that such a value never becomes the next iteration's accumulator. A proof must track every copy of A and of the
control; the natural invariant to prove is: every control-free element containing A that is not A itself lies above
every element containing X, and is merged into a control-containing element (as its head) whenever control passes it.
*Stronger empirical fact (2026-10-26).* In the generic iteration run [P, X, Z, A, J | r], the accumulator A is never
popped at all before control first returns — for every body P ≤ 10 leaves (code/a_popped.py); no element over {A, S}
other than A ever exists (bodies ≤ 9 leaves, code/kind_profile.py: element kinds only code, A, X-elements, Z/J-junk;
adjacent kinds above A: an X- or Z-element; below A: J); the weaker invariant 'no transformed element below an
X-element' holds in all 434,389 steps of bodies ≤ 10 leaves (code/invariant_check.py). *Why (partial argument).* A can
be popped only if the element D directly above it is S-headed when it reaches the front with A third; D starts as X·Z
and changes only to E·D, where E is the element directly above D. In the run's first changes E is Z, then the previous D,
so the heads of D alternate between Z and X and stay atom-headed. A proof for every body needs the same for the second
element above A (it too can change, to b·E with b arbitrary) — not done. (Superseded: the barrier lemma below proves that A is never popped by any body.)

## Barrier lemma and what it gives for loops (main agent, 2026-10-26)
*Barrier lemma — PROVED and MACHINE-CHECKED (lean/Barrier.lean, 2026-10-27: `barrier_run`, the general form — if the part above a tape r holds at least two atom-headed elements, every reachable list is L″ ++ r with at least two such elements in L″ — and `barrier_lemma` for [P, x, y] ++ r; standard axioms).* Let P be any S-term and x, y opaque. In the generic head run of [P, x, y | r] (the run stops as
soon as an element whose head is opaque is at the front), no element of the tape r is popped before the run stops.
*Proof.* After the first step the list is ch(P) ++ [y, x·y] ++ r; y and x·y have opaque heads ('barriers'). In a later
step [a, b, c] (a not a barrier, else the run has stopped): if b is a barrier, b·c is a barrier (same head); if c is a
barrier, c stays an element. So the number of barriers above r never decreases, and a barrier can pass below an element
of r only if that element is popped (as c with the barrier as b). Hence, while no element of r has been popped, at least
two barriers lie above r; an element of r at position ≤ 2 would have at most two elements above it, both barriers, one of
them at the front — so the run has already stopped. ∎
*Consequences.* (1) Every S-term behaves like a call with respect to its tape: whatever it does, it hands control to an
argument-headed element before touching anything below its two arguments. (The 'tape never popped' clause of Theorem CA
is therefore automatic.) (2) *Loop bodies never touch the accumulator* — PROVED for every body: in an iteration
[P, m̄·P, Z | T] of a numeral loop, the tape T (accumulator and everything below) is not popped before control returns,
and control returns as (m̄·P)·Z·w_1…w_k (after the first step m̄·P exists only inside (m̄·P)·Z), with w_i and all
elements between the control and T built from S, m̄·P and Z only. This proves the empirical fact of code/a_popped.py
for all bodies. (3) Between iterations the numeral step pops the two elements v1, v2 directly below the control and
re-pushes v2 and v1·v2 below the next body's arguments (after w_1…w_k). If the body leaves at least two elements of its
own below the control, the old tape is buried untouched; if it leaves exactly one (K), the next body's tape is
[w…, T0, K·T0, T1, …] — T0 unchanged on top, a transformed copy K·T0 below it, and by (2) no later body touches either;
if it leaves none, the next tape is [w…, T1, T0·T1, …] (T0 becomes the head of an element: executed later as code, or
buried). In no case does an iteration replace the accumulator on top by a transformed value, so iterated transformations
f(f(…f(T0)…)) never arise in a numeral loop with a fixed body. (The exhaustive body searches agree.) What remains open is
data-dependent control through *executing* data (case (3), T0 as a head), which is exactly the frontier of the capability
map.

## A time-to-data channel under parallel evaluation (main agent, 2026-10-26)
*Observation (COMPUTATIONALLY CERTIFIED; the reason is Lemma PH).* Put a 'clock' element W directly below the two arguments
of a call P_m (k-ary scheme, k = 2) and run until x·y reaches the front. Under leftmost-outermost evaluation W is untouched
whatever m is (barrier lemma). Under parallel evaluation W evolves one pass per head step while it waits, so its shape at
the return encodes the call's duration T_m = 2, 6, 14, 30, 62, 126 (m = 0..5): for W = SSS(SS)S(SS(SS)) its head-spine
length is 4, 3, 5, 11, 27, 60 — six distinct values, so a later opening of W behaves differently for each m
(code/clock_channel.py). For W = S(SS)SSSS the spine is 4, 4, 2, 2, 2, 2 (sizes all distinct).
*Meaning.* Under parallel evaluation the barrier lemma fails in the strongest way: waiting data is not frozen, and elapsed
time — which depends on what the head computed — becomes data that the head can later read. This is a mechanism for
data-dependent control that leftmost-outermost head runs do not have (their only data channel is executing data), so
(i) none of the leftmost-outermost limits (barrier lemma, no-accumulation, capability map) transfers to parallel
evaluation, and a non-universality proof must treat this channel; (ii) a universality construction under the weak
definition could try to use it (clocks + calls). No such construction exists yet. (No small term ≤ 9 leaves grows
linearly under parallel evaluation — code/clock_search.py — so clocks are superlinear and irregular.)

## Transfer lemma: when head-run facts survive parallel evaluation (main agent, 2026-10-26)
*Relevance.* In a head run whose list slots carry identities (a slot keeps its identity when it moves as c; the product
b·c and the spine arguments of an opened element are new slots), call a slot *relevant* if it is opened, or if it is
one of the two parts (b or c) of a product whose slot is relevant (opening b·c exposes b's spine and c itself).
Irrelevant slots are junk. [CORRECTED 2026-10-26: the first version closed relevance only under b; that was wrong —
see the correction note below.]
*Transfer lemma — PROVED (simulation argument).* If in the head run of a list K every relevant slot is a normal form
whenever it waits at position ≥ 3, then the parallel run of K (Lemma PH) opens, at every pass n, the same element as the
head run at step n; in particular every event defined by the opened shapes happens at the same time. *Proof.* Induction on
n, keeping the two runs' slots in correspondence: corresponding relevant slots hold equal terms, irrelevant ones may
differ. A parallel pass rewrites only waiting elements; relevant waiting elements are normal forms, so they are fixed by
the pass. A relevant product b·c has relevant parts b and c, equal in both runs by induction, so the product is equal; the
spine arguments of an opened (relevant, hence equal) element are equal. So opened elements coincide. ∎
*Correction note.* The first version defined relevance by closing only under b and argued that a non-relevant c could
not matter. That is false: opening b·c exposes c as a list element, whose content may have changed while c waited. The
windowed test found this on the binary counter SSS(SS)S(SS(SS)), whose parallel run first differs from its head run at
step 20 although the old test reported no relevant non-normal form (code/diverge_check.py, diverge_trace.py: the
element opened at step 20 is S·c with c reduced while waiting). With relevance closed under both parts, that term has
564 relevant waiting non-normal forms in 3000 steps, matching the divergence (code/transfer_fixed.py).
*Application (COMPUTATIONALLY CERTIFIED).* For tree calls with atomic arguments and tape, the corrected hypothesis
holds in all 146 calls re-tested (code/transfer_fixed.py); the old (b-only) hypothesis held in all 207 (k-ary levels k = 2..4, m ≤ 5, and random compositions, code/waiting_nf3.py), although 204 of them have
waiting non-normal forms (110,199 junk slots, code/waiting_nf.py); hence for these the parallel run returns x·y at exactly
the head-machine time, which explains E59's identical times. A proof of the hypothesis for every tree call is open.
*Towards the hypothesis for all tree calls.* Key fact (COMPUTATIONALLY CERTIFIED on 151 tree calls, code/xy_position.py):
in the generic run of a tree call the product x·y never lies deeper than position 2 before it reaches the front.
*Inductive sketch.* SS: [S, y, x·y] then x·y at the front. seq(A_1..A_k): Z = x·y appears as the third element after
the first two steps; inside the sub-call A_i(N_{i+1}, Z), Z is first at position 1 and is then merged as b into the junk
Z·(N_{i+1}·Z); it reappears only when the sub-call's product N_{i+1}·Z is opened (spine [A_{i+1}, N_{i+2}, Z], again
position 2), and in the last stage (A_k·S)·Z opens to [S, S, Z] (A_k = SS) or to the 3-step state of a fresh call of A_k
with product Z (A_k composite), where induction applies. The relevant non-normal forms of a tree call's run are exactly
the sub-call products (N_{i+1}·Z, (A_k·S)·Z, which are redexes), and by the key fact applied to each sub-call they never
wait; all other relevant elements are pieces of the call's code (normal forms). Writing this induction out in full would
make 'tree calls keep their head-machine times under parallel evaluation (inert arguments)' a theorem; not yet done.
*Theorem CA-par — PROVED (hand proof; checked computationally).* For every tree call C, all normal-form arguments x, y and
every tape r, the parallel (ReplaceAll) run of S C x y r … brings x·y to the head position after exactly T(C) passes, the
same shapes being opened as in the head run. *Proof.* Induction on C, proving at the same time the key fact K(C): every
list element equal to x·y lies at position ≤ 2 until it reaches the front. SS: [S, y, x·y] then the front. seq(A_1..A_k):
after two steps [A_1, N_2, Z, y·Z | r] with Z = x·y at position 2; in the sub-call A_i(N_{i+1}, Z), Z is at position 1
after one step and is then merged as b into the junk Z·(N_{i+1}·Z); no element equal to Z exists until the sub-call's
product N_{i+1}·Z is returned and opened to [A_{i+1}, N_{i+2}, Z, …] (position 2), because the only S-headed element having
Z as a spine argument is that product, which a call never opens early; the last stage opens (A_k·S)·Z to [S, S, Z, …]
(A_k = SS) or, in two steps, to [A′_1, N′_2, Z, S·Z, …], which agrees in its top three with the 2-step state of a fresh
call of A_k with product Z (the fourth element corresponds to an argument-headed element of the fresh call, so it never
reaches the front), and induction gives K. Now the relevant slots of C's run (opened, or a part b or c of a relevant
product) are of four kinds: pieces of the code of C and its sub-calls (S·N, S A N, A·S, SS — all normal forms), the
arguments x and y (normal forms by assumption), products of calls at some nesting level (x·y, N_{i+1}·Z, …), which may be
redexes but never wait, by K at that level, and S (as in S·Z). [Re-checked with the corrected relevance: 146/146 calls.] So every relevant slot is a normal form whenever it waits, and
the transfer lemma applies. ∎
*Checks:* atomic arguments — k-ary levels and 50 random calls, identical times (E59); hypothesis of the transfer lemma
on 207 calls (code/waiting_nf3.py); K on 151 calls (code/xy_position.py); normal-form arguments with x·y a normalising
redex — 13 of 13 completed runs at exactly pass T, 80 further runs skipped because their junk grows without bound under
parallel evaluation (code/par_nf_args2.py). *Scope.* Arguments must be normal forms: an argument that is itself a running
process changes while the call runs (the clock channel).

*Parallel-robust counters (corrected transfer test, PROVED for the stated windows).* For S(SS)S(S(S(SSS)))S and
S(S(SS))S(S(S(S(SS))))S (binary-type counters of the 12-leaf census, not the Theorem BC machine) no relevant slot waits as
a non-normal form in the first 3,000 steps, so by the transfer lemma their parallel runs open exactly the same elements as
their head runs for 3,000 steps (direct simulation agrees for 200 steps; longer simulation runs out of memory because
their junk grows). 37 of the 152 census counter endpoints agree with their parallel runs for at least 120 steps
(code/robust_counters.py). The Theorem BC counter is not robust (first difference at step 20). Robust counters are the
natural drivers for a clock-based (parallel-evaluation) design, since a clock is then the only source of difference.
*The robust counter's opcode word (COMPUTATIONALLY CERTIFIED to 10^6 steps; proof open).* For K0 = S(SS)S(S(S(SSS)))S,
with a = 1120421120, b_0 = 12·a, b_{k+1} = 12·b_k·42·b_k and W_k = b_k·22·b_k, the opcode word of the head run is exactly
10111204120211202211203 · W_0 · 3 · W_1 · 3 · W_2 · 3 ⋯ on all of its first 1,000,000 steps (code/k0_morphic.py). This is a
morphic word (σ(b) = 1 2 b 4 2 b, σ(h) = h b 2 2 b 3, constants fixed; τ(h) = the prefix, τ(b) = b_0), of the same
call-tree type as Theorem BC's u_{k+1} = A u_k B u_k — Conjecture R″ holds for K0 on this window. Since K0 is
parallel-robust for at least 3,000 steps (R45), its parallel run has the same opcode word there. A configuration-level
derivation (which would also prove robustness for all steps) is open; K0's 'levels' are not calls in the sense of
Theorem CA (no recurring element hands x·y back), so its return protocol differs.

## The flat binary counter K0 exactly (Theorem BC2) (main agent, 2026-10-26)
K0 = S(SS)S(S(S(SSS)))S. Levels L_0 = S(S(S(S(SSS)))S), L_{m+1} = S·M_m with M_m = (S L_m)(L_m (S L_m)) (three copies of
L_m; |L_{m+1}| = 3|L_m| + 3). Return form R′(Z) = [Z·(S·Z), S·(Z·(S·Z)), (S·Z)·(Z·(S·Z))].
*Call lemma — PROVED.* For every m ≥ 0, [L_m, x, y | r] reaches after exactly T_m = 2^{m+3} − 2 steps a list with R′(x·y)
on top, never opening x, y (the tape is untouched by the barrier lemma); the first two steps (m ≥ 1) give
[L_{m−1}, L_{m−1}·(S·L_{m−1}), x·y, y·(x·y) | r]. *Proof.* code/k0_proof.py derives the inductive step for every j ≥ 2 with
macros only at level j − 1: trace 1 2 [call j−1] 4 2 [resume j−1], so T_j = 2T_{j−1} + 2; base cases m = 0, 1 concrete
(code/k0_behaviour.py: R′(x·y) on top after 6 and 14 steps); the continuation lemma follows as for Theorem BC. ∎
*Theorem BC2 — PROVED.* For every k ≥ 1 a list with R′(M_{k−1}) on top reaches R′(M_k) on top after exactly
2T_k − 1 = 2^{k+4} − 5 steps (code/k0_proof.py: 3 [resume k] 2 2 [resume k], nothing below the top used). The head run
of K0 has R′(M_0) on top at step 22 (direct computation; note M_{k−1}·L_k = M_{k−1}·(S·M_{k−1}), so this is the
configuration [M_{k−1}·L_k, S·(M_{k−1}·L_k), L_k·(M_{k−1}·L_k)] seen at the opcode-3 events). Hence it has R′(M_k) on top at
step 32·2^k − 5k − 10 for every k ≥ 0, it has no normal form, and its opcode word is
10111204120211202211203 · W_0 · 3 · W_1 · 3 ⋯ with W_k = u_k·22·u_k, u_{k+1} = 12·u_k·42·u_k, u_0 = 12·1120421120 —
morphic. ∎ (Certified independently on the first 10^6 steps, code/k0_morphic.py.)
*Meaning.* A second, structurally different binary counter (three copies per level, return form R′) proved exactly; it is
also the counter that runs identically under parallel evaluation for at least 3,000 steps (R45). Proving that robustness
for all steps needs the transfer hypothesis inside its calls (as for Theorem CA-par) — not done.
*K0 is parallel-robust (PROVED for 200,000 steps; argument for all steps).* The efficient windowed transfer test
(code/transfer_fast.py: each slot's normal-form status checked when it first waits; relevance closed under both product
parts) finds no relevant slot waiting as a non-normal form in the first 200,000 steps of K0's head run (124,757 waiting
non-normal-form slots, all junk), so by the transfer lemma K0's parallel run opens exactly the same elements as its
head run for 200,000 steps. (Same test: 564 violations for SSS(SS)S(SS(SS)) in 3,000 steps, as before.)
*All steps (argument, same pattern as Theorem CA-par).* Induction on the level m of a call [L_m, x, y | r] occurring in
the run: (i) x is merged into Z = x·y at the first step and y, after one step at position 1, into the junk y·Z, so neither
waits; (ii) Z lies at position ≤ 2 whenever it is an element: [M, y, Z], [L_{m−1}, L_{m−1}(S L_{m−1}), Z, y·Z]; inside the
inner call Z is at position 1 once and is then merged into junk; it is exposed again only when the inner return value
Z′(S Z′) (Z′ = L_{m−1}(S L_{m−1})·Z) is opened to [M_{m−2}, S L_{m−1}, Z, S Z′, …] and then to the resume state
[L_{m−2}, L_{m−2}(S L_{m−2}), Z, …] — position 2 each time; (iii) inner products Z′ never wait by induction; (iv) the
return values S·(Z′(S Z′)) and (S Z′)·(Z′(S Z′)) and the elements (S L_{m−1})·Z, S·Z′ that are pushed below a resume state
form the resumed call's tape, never popped (barrier lemma) and never reached afterwards (the unknown rest of the
derivations), so they are irrelevant; (v) code pieces (L, M, L(S L), S L) are normal forms. The driver cycle
3 [resume k] 2 2 [resume k] adds only resumed-call tapes of the same kind. So every relevant slot is a normal form
whenever it waits, and the transfer lemma gives: *K0's parallel run coincides with its head run forever.* This is a
hand argument at the level of rigour of Theorem CA-par (not machine-checked beyond 200,000 steps).

## Control flow is order-independent; clocks cannot steer (main agent, 2026-10-26)
*Proposition CF — PROVED (from standard facts).* Let F be an S-term at the front with arguments x, y and tape r, and
read the list as the term t = S·F·x·y·r_1⋯. If some reduction of t reaches a head normal form whose head is one of the
argument variables, then every reduct of t — in particular the term obtained by first reducing F, x, y or the r_i in any
order, any number of steps — reaches a head normal form with the same head variable and the same number of arguments,
with arguments convertible to the first ones; and head reduction (hence every order that keeps contracting the head
redex, such as leftmost-outermost and parallel evaluation, Lemma PH) reaches it. *Proof.* Church–Rosser for S-reduction
(F2 above): t′ =_conv t; head normal forms of convertible terms have the same head and arity and convertible arguments
(standard consequence of confluence: a common reduct of two head normal forms keeps both heads and arities); by the
standardization theorem head reduction finds a head normal form whenever one exists, and inner steps interleaved with
head steps do not prevent this. ∎
*Consequences.* (1) *No timeout branches:* a delay term's states D_t are reducts of D, so [D_t, c1, c2 | r] hands control
to the same continuation for every t (confirmed: no branch among all delay terms ≤ 9 leaves, code/timeout_branch.py).
(2) *The clock channel (R43) cannot steer control:* elapsed time changes the syntax of what is opened and the timing,
never which argument receives control or (up to conversion) what it receives. So the sequence of control transfers of a
computation — its Böhm-tree-level behaviour — is the same under leftmost-outermost, parallel and any head-fair order.
(3) What remains order-dependent is purely syntactic: a detector that reads intermediate terms (not head-normal-form
events) can see different syntax under different orders. A universality construction exploiting the order would have to
live entirely in such syntactic differences; a non-universality proof must show that detectors cannot extract universal
power from them. This sharpens item 1 of the outside checklist: control flow transfers across orders for free; only
detector-visible syntax does not.

## Automatic exact-structure proofs for counter head runs (main agent, 2026-10-26)
code/auto_prover.py mechanises the method of Theorems BC, TC, K and BC2 for a given term: (1) a *level family* — frequent
front elements whose generic run returns the same top three R and whose times grow geometrically, each containing the
previous; (2) the *scheme* F with L_{m+1} = F[L_m] (holes = occurrences of L_m), verified on the whole family; (3) the
*return form* R(Z), required to be a function of Z = x·y alone; (4) the symbolic engine with level tokens (unfold by F,
fold F[L(e)] → L(e+1)), CALL (call lemma) and RESUME (continuation) macros, the resume pattern being computed
symbolically as the state of a level-(d+1) call just before its first inner call; (5) the call lemma's inductive step for
all j ≥ jmin with macros only below level j; (6) the driver R(G[L(0)]) → R(G[L(1)]) for a context G found from the
concrete run's events. *Soundness conditions checked per term:* the base levels below jmin are consecutive members of the
family and satisfy the call lemma concretely; every element below the top three of the resume state has an argument as
its head (so the remainder of a fresh call never opens it; otherwise the term is reported 'unsafe' and not counted);
the event used to start the driver lies at a level ≥ the driver's jmin and is reached by the concrete run (transient);
plus an independent cross-check — the gap to the next driver event predicted from the derived trace and the concrete call
times equals the gap in the real run.
*Census result (E62).* Of the 152 counter-type endpoints of the 12-leaf census, 144 are PROVED exact this way — all 111
binary counters and 33 of the 40 base-2 'OTHER' runs — each with a passing cross-check; 2 OTHER runs fail the resume
soundness check (not counted); 5 OTHER runs and the nested counter have no level family (non-call mechanisms). Each proof
gives the run's exact recursive structure and hence a morphic opcode word: Conjecture R″_{3,d} (first three elements)
holds for these 144 runs.
*Correction and strengthening (later, 2026-10-26).* The cross-check above compared one predicted gap per term — every
one of the 144 proofs reported '1/1' — so it was a thin sanity check (the proofs themselves are the symbolic derivations).
It is replaced by an independent numerical test (strong_check in code/auto_prover.py): (i) the derived call-step
recursion (cost of the call-step trace in terms of lower call times) must reproduce the concrete generic call time of
every family level it applies to; (ii) levels beyond the observed family are built with the scheme L_{m+1} = F[L_m] and
their call times with the recursion, and every gap between consecutive driver events (or first appearances of a level at
the front, for template drivers) in the first 400,000 steps of the concrete run must equal the cost of the derived driver
trace. Level detection was also corrected: a group of fronts with one return form can contain other fronts besides the
levels, so besides the original greedy chain the longest containment chain with increasing call times is tried, and a
group is no longer discarded when its three largest members are not levels. Re-run results: EXPERIMENTS E66.

*RESUME by the barrier criterion (later, 2026-10-26; made the only criterion after an audit).* The head test (every item
below the resume state's top three headed by an argument) is NOT sufficient on its own: the generic call returns at the
first opening of an argument-headed element, and that event could itself be the opening of one of those lower items, in
which case the remainder's result would depend on them. The call prover therefore no longer accepts it; RESUME is
accepted only when the remainder of the call, run symbolically from the resume
state's top three with the unknown rest directly below (inner call by CALL; resumes only at strictly lower levels, so the
induction on levels is well founded), returns R(x·y) without any element of that rest reaching the top three — then the
remainder never reads below its top three and RESUME is sound whatever lies there. The symbolic run covers the inner levels
from its jmin on; the lower inner levels are checked concretely: in the generic call of the next level, everything below
the resume state's top three is replaced by fresh atoms, and the remainder must return R(x·y) without any of them
reaching the top three. Two counters are proved this way (E71). (The hand-built proofs of Theorems BC, TC, K and BC2
are not affected: their continuation lemmas check both conditions the head test lacks — the lower elements are never
opened before the return, and none of them occurs in the final three terms — so the remainder's result is the same
for every content below the first three.)
*Corollary CA′ (whole list for call runs) — PROVED per term when the replays below succeed (code/call_residue.py).* The
call prover's macros leave everything below the return form unknown; replaying its derivations exactly gives the whole
list. (a) CALL: [L(j), x, y] ++ r →* R(x·y) ++ RES(j, x, y) ++ r, where for j ≥ jmin RES(j) is the list between R(x·y) and
the unknown rest at the end of the exact replay of the call step (inner calls and resumes leave RES/REM items at lower
levels — a recursive list grammar), and for the base levels it is the concrete residue of the generic call (the generic
run never pops its tape). (b) RESUME: [pattern(Z)] ++ r →* R(Z) ++ REM(d, Z) ++ r, where REM is read off an exact run of
the remainder of a level-(d+1) call from its resume point with the unknown rest directly below the top three (symbolic for
the inductive levels; for base levels the concrete remainder is run with the items below replaced by fresh atoms) — so
the remainder provably never reads below its top three; otherwise no certificate is given. (c) The driver's exact replay
gives the residue D pushed between consecutive events: the list at event k is top(k) ++ D(k−1) ++ ⋯ ++ D(k_s) ++ (the
concrete list at a base event). Residue items never reach the top three in these replays, so they follow the original
proofs' trajectories exactly. Every list entry is thus generated by the residue grammar; cut at depth d the items take
finitely many shapes, and the window word at each level is a fixed pattern of the window words of the inner calls in
finitely many contexts — a morphic word. So R″_{k,d} holds for every k for these terms. Numerical test: at every driver
event in the first 300,000 steps the first 30 predicted entries (residues expanded recursively) equal the concrete ones.
For the binary counter SSS(SS)S(SS(SS)) the call-step residue has 7 items (two inner residues among them), matching the
measured residue sizes 1, 2, 9, 23, 51, 107, 219, 443 (r_j = 2 r_{j−1} + 5) of its levels.

## Comb runs (single counters) proved exactly (main agent, 2026-10-26)
*Example — PROVED.* For SS(S(SS))(SS)SS(S(SS)), with λ = S(SSS), C_0 the base reached by the run and C_{m+1} = λ·C_m:
(L) block lemma — from [SSS, λ·T, λ·E′ | r] the head run reaches [SSS, T, λ·E′ | r′] after 6 steps (opcodes 202203), for
opaque T, E′, r (symbolic); hence by induction the loop [SSS, C_n, E | r] →^{6n} [SSS, C_0, E | r_n] whenever E is a comb;
(D) driver — with comb tokens, [SSS, C_0, C_{j+2}] reaches [SSS, C_{j+1}, C_{j+3}] after 13 steps for every j ≥ 1 (symbolic,
never reading the unknown rest); (T) the concrete run reaches a cycle start [SSS, C_n, C_{n+2}] (e.g. step 13397, n = 65).
So cycle n takes 6n + 13 steps forever and the opcode word is D·B^n·D·B^{n+1}⋯ (morphic). ∎
*Automation.* code/comb_prover.py finds the block word B (trying every rotation), checks that every block except the last of
its run starts with the same front F and peels the same layer λ off the second element, proves (L) symbolically (third
element opaque or a λ-comb), reads the cycle starts as combs over one base (X = C_n, E = C_{n+c}), derives (D) with comb
tokens, and cross-checks every observed cycle length against n·|B| + (driver steps). Proved with complete cross-checks:
SS(S(SS))(SS)SS(S(SS)) (47/47 cycles), S(SSS)S(SSS) (46/46), SS(SSS)S(SS)SSS (B = 30023003, λ of 6 leaves, 18-step driver,
41/41); S(S(S(SS))S)(SSS)(SS) fails the block lemma (another shape).

## Loop runs proved exactly: the loop prover (Theorem LP) (main agent, 2026-10-26)
*Patterns.* Terms over S, opaque atoms and comb tokens T(F, X, b) := F^{n+b}(X) (n a symbolic integer; F a concrete
context with one or more holes, all filled with the same term; X concrete, not of the form F(_)). Right combs λ^{n+b}·X are
the case F = λ·□; a linked list whose every link refers to the next link twice is a two-hole context. The head machine
acts on patterns: a token at the head of a spine is unfolded (F^{n+b}(X) = F(F^{n+b−1}(X)), valid for n ≥ 1 − b; the
condition is recorded in n_0; a context whose spine head is the hole would make opcodes depend on n and is rejected), and a
product equal to F(T(F, X, b)) is folded to T(F, X, b+1). Below a finite window lies the unknown rest r; a symbolic run fails as soon as an element of r reaches the first
three positions (so r is never read, consumed or copied) or an opaque head would be opened.
*Lemma LB (loop lemma) — PROVED.* Let A be a window of h patterns in which a variable V occurs (as F^k(V), k ≥ 0), and
suppose the symbolic run from A(F(O)) (O opaque, r unknown) reaches after L steps a state whose first h elements are A(O).
Then for every m ≥ 0, every closed X and every rest r: A(F^m(X)) ++ r →^{mL} A(X) ++ r′ for some r′.
*Proof.* The run neither opens O nor reads r, and instantiation commutes with head steps, so A(F(T)) ++ r →^L A(T) ++ r″
for every term T and rest r; apply this with T = F^{m−1}(X), F^{m−2}(X), …, X (induction on m). ∎
*Lemma LC (cycle lemma) — PROVED (schema).* Let M(n) be a window pattern. Suppose the symbolic run from M(n) — ordinary
steps, plus jumps over loops by Lemma LB (a loop of m = n + b blocks, valid for n ≥ −b) — reaches, for symbolic n, a state
whose first |M| elements are M(n+1) (every token offset +1), never reading the rest. Then M(n) ++ r →* M(n+1) ++ r′ for
every n ≥ n_0 and every r, in αn + β steps. ∎
*Theorem LP — PROVED for every term certified by code/loop_prover.py (computer-assisted).* If the head run of t reaches
an instance M(n_1) with n_1 ≥ n_0, then from there it is, forever, the cycle M(n) →* M(n+1) for n = n_1, n_1 + 1, …; the
opcodes of a cycle are u_0 B_1^{n+b_1} u_1 B_2^{n+b_2} ⋯ u_k with fixed words u_i, block words B_i and offsets b_i (opcodes
of pattern steps do not depend on n: unfolding a token adds exactly the arguments of the spine of F), so the opcode word of t
is a finite prefix followed by ∏_{n ≥ n_1} u_0 B_1^{n+b_1} ⋯ u_k — a morphic word. Every d-window word is morphic as well
(the depth-d cut of F^m(X) is constant once m ≥ d). So Conjecture R″_{3,d} holds for t, for every d (the symbolic run
knows the first three elements at every step; deeper window positions are not determined by the certificate). ∎
*How the prover finds and checks the proof.* (1) Block word and cycle starts from the opcode word (maximal B-runs; the
driver sequence must be periodic and the loop counts must grow by one per period; the four best-scoring block lengths and
all rotations are tried, shortest block first, and the first candidate that yields a certificate is used — the choice
only affects whether a certificate is found, never its validity). (2) W(n) by anti-unifying the windows
at two consecutive cycle starts (every difference must be a comb one layer longer, giving tokens; contexts larger than
5,000 nodes are rejected; a second pass replaces every subterm pair that is two consecutive members of an already found
family by that family's token, which handles coupled recurrences — an element built from another element's comb),
checked on a third.
(3) Symbolic run from W(n); loops are recognised either (a) when a list element is a token and one block of the observed
length preserves the window prefix with that element peeled once, or (b) by comparing the window with the one L steps
earlier: every difference must be a token one layer lower, all of the same family (F, X) — those occurrences become F^k(V)
(this covers loops that carry the variable in several places, e.g. an element below the peeled comb rebuilt from it in
every block); Lemma LB is then checked symbolically and the loop is jumped. (4) The cycle closes when a later loop starts
from M(n+1) up to j blocks of its own loop (M = the window at the first loop). (5) Transient: the concrete run reaches
W(n_1) with n_1 ≥ n_0 (instance check). (6) Independent numerical cross-check: for every later cycle in the first 60,000
steps, the concrete state at the predicted times is an instance of M(n) and of M(n+1).
*Results (all with complete cross-checks).* The three comb_prover examples; S(S(S(SS))S)(SSS)(SS), which comb_prover
could not do; two-loop cycles S(S(SS)SS)S(SS) and SSSS(S(SS(SS)S))SS (cycle 10n + 25; in the first, the loop peels a comb
in the third list position and pushes one element below the fourth per block); two-place loops S(S(S(S(SSS)(SSS))))SS
(8n + 13) and S(S(SS))SS(SSS)(S(SS)) (8n + 16); linked-list walks with two-hole contexts, e.g. S(SSS(S(SS))S)(SSS)S, whose
chain is c_i = F(c_{i+1}) with F = S □ (S P c (S □)) for fixed P, c (cycle 2n + 22, 158/158 cross-checks). On the census
sample, together with the call and comb provers: all 150 sampled non-counter endpoints are proved exact (EXPERIMENTS
E67; the loop prover supplies 66 of them, e.g. coupled recurrences such as SS(SS)S(S(SS))S(SS)S and runs with up to 15
loops per cycle).
*Corollary LP′ (whole list, every window size) — PROVED per certified term when the residue pass succeeds.* Lemma LB
also yields the block's pushes: one block maps A(F(T)) ++ r to A(T) ++ P(T) ++ r, so m blocks map A(F^m(X)) ++ r to
A(X) ++ P(X) ++ P(F X) ++ ⋯ ++ P(F^{m−1} X) ++ r — a graded segment. Re-running the certified cycle along the same
trajectory with these segments (and the known items below each window) kept, and only the part B(n) below the anchor's
window left unknown, gives the cycle's residue R(n): the full list at the anchor of cycle n+1 is M(n+1) ++ R(n) ++ B(n),
so after the transient the whole list at every anchor is M(n) ++ R(n−1) ++ R(n−2) ++ ⋯ ++ R(n_s) ++ B(n_s) with B(n_s)
concrete, and inside a cycle every intermediate list is known as well (block states with the pushes so far). Hence every
(k, d)-window word is determined by the certificate; its letters depend on token counts and segment positions only
through values cut off at d, so each cycle reads fixed words around runs that grow by one per cycle — a morphic word.
So R″_{k,d} holds for every k and d for these terms, which is what Proposition UB needs for detectors that halt in bounded
time on head-first strings. Numerical test: at every later anchor in the first 60,000 steps, the first 30 list entries
predicted by M(n) ++ R(n−1) ++ ⋯ ++ B(n_s) equal the concrete ones (code/loop_prover.py, 'whole list' line). The call
prover's certificates are not yet extended this way (their CALL/RESUME macros leave everything below the return form
unknown), so for call-certified terms only R″_{3,d} is established.
*Scope.* Like the other provers this is a per-term certificate (a finite symbolic computation per term); it proves
Conjecture R″ only for the certified terms, not in general.

*Lemma NW (countdown words are morphic) — PROVED.* Let D_m = A^m s A^{m−1} s ⋯ A s. The word Z D_1 t D_2 t D_3 t ⋯ is the
fixed point σ^ω(Z) of σ: Z ↦ Z A s t, A ↦ A, s ↦ A s, t ↦ A s t. *Proof.* σ(A^k s) = A^{k+1} s, so σ(D_m) = D_{m+1} with
its last factor A s removed, and σ(D_m t) = σ(D_m) A s t = D_{m+1} t; hence σ^k(A s t) = D_{k+1} t and σ^n(Z) =
Z D_1 t D_2 t ⋯ D_n t. ∎ (Checked by machine up to m = 8.) With a non-erasing coding (A, s, t ↦ fixed opcode words) this
covers the countdown runs S(SS)S(S(S(SSS)(SS)))S etc. (E71), whose opcode words have the form u ∏_m D_m τ — once their
structure is proved (not done yet: it needs a nested induction, an inner count running down from the outer one).

## Nested loops: square runs proved exactly (Theorem NL) (main agent, 2026-10-26)
*Setting.* As in Theorem LP, plus: (i) *exact macros* — by Lemma LB with pushes, a loop of m = n + b blocks maps
A(F^m(X)) ++ r to A(X) ++ G(P, F, X, b) ++ r, where the segment G(P, F, X, b) = P(X) ++ P(F X) ++ ⋯ ++ P(F^{m−1} X) is
kept symbolically and popped group by group when it reaches the first three positions (each pop records n + b ≥ 1);
(ii) *nested block lemma* — A(F(O)) →* A(O) ++ P(O) proved by a symbolic run (O opaque, unknown rest below) that may itself
apply loop macros on tokens in n, so one block takes τ(n) steps, a polynomial; inner segments may not depend on O;
(iii) loops detected by comparing the window with every earlier window of the run, across macros; step counts are
polynomials in n, a loop of n + b blocks of τ(n) steps taking (n + b)·τ(n).
*Lemma NL (nested loop lemma) — PROVED.* If the nested block lemma holds for A, F (for all n ≥ n_0 and every term O), then
for every m ≥ 0: A(F^m(X)) ++ r →^{m·τ(n)} A(X) ++ P(X) ++ ⋯ ++ P(F^{m−1}X) ++ r. *Proof.* Induction on m; within one
round n is fixed, and the block lemma holds for every O, in particular O = F^{m−1}(X). ∎
*Cycle lemma, soundness.* Pass 1 runs the cycle with exact macros (unknown rest only below the cycle start W(n)) and finds
the closure M(n) →* M(n+1) at an anchor; pass 2 repeats it with the unknown rest directly below the anchor's window and
must reach the same closure, so the cycle never reads below the anchor window and M(n) ++ r →* M(n+1) ++ R(n) ++ r for
every r — the induction of Lemma LC goes through with a polynomial cycle length.
**RETRACTION (2026-10-26, later): the two square-run certificates below are WITHDRAWN.** A soundness audit found that
nested block lemmas used the same opaque atom O for the outer loop variable and for the inner block lemmas run inside them,
so the engine could not tell the two unknowns apart (an inner block that swapped them would still have passed the check).
With a distinct atom per nesting depth the two square runs are no longer proved. Their numerical instance checks did pass
(18/18, 26/26), so the structure claims were EXPERIMENTALLY SUPPORTED only, until re-proved. Lemma NL and the method are
unaffected as statements. **Re-proved (later the same day)** with the corrected implementation: a distinct opaque atom
*and* a distinct loop-variable atom per nesting depth, and segments that carry their own variable, so an inner loop's
pushes may mention both its own variable and the outer one (the first fix alone made the proofs fail: the inner segment
really does depend on the outer variable, which the shared atom had silently mislabelled). See E77.
*Theorem NL — PROVED for every term certified by the corrected code/nest_prover.py (computer-assisted).* Two square runs of E73:
S(S(SS))S(S(S(SS))S)(S(S(SS))SS(SS)) — round n takes 12n² + 11n + 5 steps (n ≥ 2), its repetition loop's block contains an
inner loop of n + c blocks; S(SSSS)SS(S(S(S(SSSS)(S(SS)))(SS(S(SS)S(SS))(SS))))(SS)S(SS(SS)) — 4n² + 11n + 5 steps. Instance
cross-checks 18/18 and 26/26 (the concrete state at the predicted times is an instance of M(n) and M(n+1)). Their window
words are nested-loop words with affine counts, hence effectively profinitely ultimately periodic (Lemma PUP): R″_PUP holds
for them. They are NOT morphic (Theorem NM below, via Lemma S). *Literature (T. Smith, 'A characterization of morphic words
with polynomial growth', DMTCS 22 (2020), arXiv:1903.09905):* an infinite word is morphic with growth Θ(n^k) iff it is a
zigzag word of depth k, α = q ∏_{i≥1} R(l, i), where each term of the fixed list l is a static string or a product of
inner rounds over j = 1..i (forward) or i..1 (backward). So R(l, i+1) arises from R(l, i) by insertions at a bounded number
of places, while a square round (a^n b)^n needs about n insertions to become (a^{n+1} b)^{n+1}. This strongly suggests that
square words are not morphic with polynomial growth; a proof must still handle zigzag pieces not aligned with the square
word's rounds, and representations of exponential growth (the Diekert–Krieger dichotomy covers pure morphic words only).
Not covered: countdown runs (there the inner
count is the loop variable itself, so the block lemma would need a second symbolic variable).

## Morphic R″ is false: two square runs have non-morphic window words (Lemma S, Theorem NM) (main agent, 2026-10-26)
*Lemma S (sparse markers in morphic words) — PROVED.* Let w be a morphic word and β a nonempty finite word such that every
factor of w containing two (possibly overlapping) occurrences of β occurs only finitely often in w. Then the number of
occurrences of β that start among the first N positions of w is O(√N).
*Proof.* By Cobham's theorem (Allouche–Shallit, *Automatic Sequences*, 2003, §7.5) w = τ(y), y = h^ω(x), with h a
non-erasing morphism over a finite alphabet A, h(x) = x u (u nonempty) and τ a coding. Then y = x u h(u) h²(u) ⋯.
(1) Let A_∞ be the letters occurring infinitely often in y. A letter outside A_∞ occurs in only finitely many of the words
h^k(u), so for some K every h^k(u) with k ≥ K lies in A_∞^+. Put v = h^K(u) = c_1 ⋯ c_r; then
y = x u ⋯ h^{K−1}(u) · h^0(v) h^1(v) h^2(v) ⋯.
(2) For c ∈ A_∞ and n ≥ 0, τ(h^n(c)) occurs in w at infinitely many positions: y = h^n(y) = h^n(y_0) h^n(y_1) ⋯, so each
occurrence y_p = c gives an occurrence of h^n(c) at position |h^n(y_0 ⋯ y_{p−1})|, and these positions increase strictly
with p because h is non-erasing. Hence, by the hypothesis, each word τ(h^n(c_i)) contains at most one occurrence of β.
(3) ℓ_n = |h^n(v)| is nondecreasing (h is non-erasing). If ℓ is bounded, the words h^n(v) range over a finite set and
h^{n+1}(v) = h(h^n(v)), so w is ultimately periodic; then β occurs only finitely often (two occurrences beyond the
preperiod would span a factor that recurs with the period, against the hypothesis) and the claim is trivial. So let ℓ be
unbounded. If ℓ_n = ℓ_{n+t} with t ≥ |A|, every letter c of h^n(v) has |h^i(c)| = 1 for 0 ≤ i ≤ t, so its trajectory
c, h(c), …, h^t(c) repeats a letter and |h^i(c)| = 1 for all i; then ℓ is constant from n on — impossible. Hence
ℓ_{n+|A|} ≥ ℓ_n + 1 and ℓ_n ≥ n/|A|.
(4) Count. Write w = P · T_0 T_1 T_2 ⋯ with P = τ(x u ⋯ h^{K−1}(u)) and tiles T_n = τ(h^n(v)), each the product of the r
sub-tiles τ(h^n(c_i)). An occurrence of β starting in a sub-tile either lies inside it (at most one, by (2)) or starts
among its last |β| − 1 positions, so at most |β| occurrences start in each sub-tile. Tile T_n starts at position
≥ Σ_{j<n} ℓ_j ≥ n(n − 1)/(2|A|), so fewer than 2 + √(2|A|N) tiles start before N, and at most
|P| + r·|β|·(2 + √(2|A|N)) occurrences of β start before N. ∎
*Remarks.* No assumption on the growth of h (polynomial or exponential) is needed. Example: ∏_{m≥1} (a^m b)^m is not
morphic — each factor b a^m b occurs m times, yet b occurs Θ(N^{2/3}) times among the first N letters; ∏_m a^m b is
morphic with Θ(√N) letters b, so the bound is sharp.

*Certified opcode words (code/nest_words.py).* The Theorem NL certificate fixes every step of the cycle M(n) →* M(n+1):
each symbolic step has a definite opcode (the engine computes the head element's spine), and a loop macro of n + b blocks
contributes its block's opcode word n + b times (inner macros inside a block likewise). Recording them gives the run's
opcode word from the first anchor on as ∏_{n ≥ n_1} C(n) for all n — read off the proof, not observed. For
t_1 = S(S(SS))S(S(S(SS))S)(S(S(SS))SS(SS)), with Q = 014110110204, E = 01411011020501031020402 and
G = 0141101102050103102050103102 (opcodes as digits): C(n) = Q^{n−2} (E Q^{n−1})^{n−1} G Q for n ≥ 19, from step 27,311
on. For t_2 = S(SSSS)SS(S(S(S(SSSS)(S(SS)))(SS(S(SS)S(SS))(SS))))(SS)S(SS(SS)), with q = 0104, D = 0105,
F = 01031020402 and H = 0103102050103102: C(n) = q^{n−2} D (F q^{n−1} D)^{n−1} H q for n ≥ 27, from step 28,846 on.
(Bookkeeping test, not part of the proof: |C(n)| equals the certified cycle length, and the expansions of 14 resp. 12
consecutive C(n) equal the concrete opcode words — 115,969 and 55,622 steps.)
*Theorem NM — PROVED (computer-assisted: the Theorem NL certificates of t_1 and t_2; Lemma S and the word combinatorics
by hand).* The opcode words of the head runs of t_1 and t_2 are not morphic. Consequently, for every k ≥ 3 and d ≥ 6,
their (k, d)-window words are not morphic: Conjecture R″_{k,d} in its morphic form is FALSE.
*Proof for t_1.* Let O = P · O′ with O′ = C(19) C(20) ⋯ and P the first 27,311 opcodes. (i) The letter 5 occurs in E once
(offset 11), in G twice (offsets 11 and 20), and not in Q. An occurrence of E has its 5 at offset 11. If that 5 is an
E-block's, the occurrence is that E-block; if it is G's first 5, the occurrence starts at G's start, but E and G differ
at offset 20 (4 vs 5); if it is G's second 5, it starts at G's offset 9, but G[9..11] = 205 ≠ 014. So the occurrences of
E in O′ are exactly the E-blocks, n − 1 of them in C(n). (ii) Q, E and G agree on their first 11 letters, and Q differs
from E and G at offset 11 (4 vs 5). After an E-block of C(n) comes Q^{n−1} and then E or G; C(n) ends with G Q and C(n+1)
begins with Q^{n−1}. So the factor from one occurrence of E to the end of the next is E Q^{n−1} E inside C(n), or
E Q^{n−1} G Q^n E across C(n), C(n+1). By the offset-11 comparison, E Q^k E occurs only inside C(k + 1), and
E Q^k G Q^{k+1} E only at the junction of C(k + 1) and C(k + 2). Every factor containing two occurrences of E contains
one of these, so it occurs only finitely often in O′, hence in O. (iii) C(19) ⋯ C(M) has length
Σ (12n² + 11n + 5) ~ 4M³ and contains Σ (n − 1) ~ M²/2 occurrences of E, so E occurs Θ(N^{2/3}) times among the first
N letters of O — not O(√N). By Lemma S, O is not morphic.
*Proof for t_2.* The same, with marker F. The letter 3 occurs in F once (offset 3), in H at offsets 3 and 12, and not in q
or D. An occurrence of F at H's start fails at offset 8 (4 vs 5); one whose 3 is H's second starts at H's offset 9 and
reads 0103102 0104…, failing at offset 8 (1 vs 4). So the occurrences of F are the F-blocks, n − 1 per C(n). Since q and
D differ at offset 3 (4 vs 5) and F and H at offset 8, F q^k D F occurs only inside C(k + 1) and F q^k D H q^{k+1} D F only
at one junction; C(n) has length 4n² + 11n + 5, so F occurs Θ(N^{2/3}) times. ∎
For the window words: the opcodes are at most 5, so for d ≥ 6 the opcode is a function of the (k, d)-window letter, and a
coding of a morphic word is morphic. (Sanity test, code/nest_words.py with a marker argument: per-cycle counts n − 1, and
every factor between consecutive markers confined to one cycle, on 10 cycles of each run.)
*A third square run (later the same day, 320–640-leaf hunt, E87).* t_3, a 444-leaf endpoint (the term is recorded in
data/sample_hunt_320_640.tsv, prover nest_prover.py), has cycle length 5·n² + 11·n + 5 and certified cycle word
C(n) = Q^{n−2} (E Q^{n−1})^{n−1} G Q with Q = 01204, E = 0120501031020402, G = 012050103102050103102 (n ≥ 25, from step
27,941). The proof for t_1 applies verbatim with other offsets: the letter 5 occurs in E once (offset 4) and in G twice
(offsets 4 and 13), not in Q; E and G first differ at offset 13 (4 vs 5); G[9..12] = 1020 ≠ 0120 = E[0..3]; Q differs
from E and G at offset 4. So E occurs exactly at the E-blocks (n − 1 per cycle), every factor between consecutive
occurrences lies in one cycle, and E occurs Θ(N^{2/3}) times: **t_3's opcode word is not morphic either** (opcodes ≤ 5
in the transient and in C(n), so the window statement holds for d ≥ 6). Sanity test as before: per-cycle counts n − 1,
all 19 inter-marker factors confined to one cycle (10 cycles); expansion equals the concrete run.
*Consequences.* (1) Conjecture R″ in its morphic form is refuted by concrete terms (13, 33 and a 444-leaf endpoint); the doubt
recorded in 'Weakening the bridge' and after Theorem NL is resolved. (2) Nothing is lost for the bridge: Proposition UB
only needs R″_PUP (Carton–Thomas), these runs satisfy it (Lemma PUP), and every run proved so far is PUP. The structural
conjecture for leftmost-outermost runs is now R″_PUP alone. (3) This is a fact about one evaluation order; it neither
proves nor refutes universality.

## The countdown run S(SS)S(S(S(SSS)(SS)))S, exact (Theorem CD) (main agent, 2026-10-26)
*Setting.* t_c = S(SS)S(S(S(SSS)(SS)))S is one of the five census counters no automatic prover handles (a 'countdown'
run: epoch m contains inner loops of m−4, m−5, …, 1 blocks). Let X_1, X_2, … be the first list elements at its epoch
starts (the steps after which the opcode word ends in 2201), and put T_k := S (S X_k) (S S (S X_k)) and, for k ≤ e,
Ch(e, e) := T_e, Ch(k, e) := S S (S X_k) Ch(k+1, e) (k < e) — a chain through the heads X_k, …, X_e.
*Theorem CD — PROVED (symbolic lemmas checked by code/countdown_proof.py; induction by hand; transient concrete).*
For every m ≥ 3 the run passes through the epoch start E_m = [X_m, S S (S X_m), T_m] ++ r_m, the heads satisfy
X_e = Ch(1, e−1) for all e ≥ 2 (each head is a chain through all earlier heads), and E_{m−1} → E_m takes m² − 3m + 10
steps with opcode word 3 · D_{m−4} · 0212130212201, where D_j = (03)^j 0213 (03)^{j−1} 0213 ⋯ (03)^1 0213 (D_0 empty).
So t_c has no normal form and its opcode word is a countdown word, morphic by Lemma NW.
*Lemmas (each checked by a symbolic head-machine run with the named parts as opaque atoms and unknown junk below; the
junk never reaches the first three positions and no atom is opened):*
W  [S, S X_k, Ch(k+1, e), R] ++ r →² [S, S X_{k+1}, Ch(k+2, e), R, S X_k Ch(k+1, e) R] ++ r for k + 1 < e (opcodes 0 3);
E  [S, S X_{e−1}, T_e, R] ++ r →³ [X_e, R, S S (S X_e) R, S X_{e−1} T_e R] ++ r (opcodes 0 2 1);
O  [S S (S X_1) C, R′, R″] ++ r →¹ [S, S X_1, C, R″, R′R″] ++ r (opcode 3);
B  [X_2, R, S S (S X_2) R, S X_1 T_2 R] ++ r →^10 [X′, S S (S X′), T(X′)] ++ r′ with X′ = S S (S X_1)(S S (S X_2) R), for
   opaque R, with X_1, X_2 the concrete heads (opcodes 2130212201).
*Proof.* Induction on m; X_e = Ch(1, e−1) defines every head from X_1, X_2 by recursion, and the claim is that the run's
heads are these terms. Assume the run is at E_{m−1} with X_{m−1} = Ch(1, m−2) = S S (S X_1) Ch(2, m−2) (m − 1 ≥ 3). By O,
E_{m−1} → Φ(m−2, T_{m−1}) ++ …, where Φ(e, R) := [S, S X_1, Ch(2, e), R]. *Step lemma:* for 3 ≤ e ≤ m−2,
Φ(e, R) →^{2e} Φ(e−1, S S (S X_e) R): W for k = 1, …, e−2 walks the chain to [S, S X_{e−1}, Ch(e, e), R], E gives
[X_e, R, S S (S X_e) R, …], and O (with X_e = S S (S X_1) Ch(2, e−1), valid for e ≥ 3) gives Φ(e−1, S S (S X_e) R). The
carried element starts as R_{m−2} = T_{m−1} = Ch(m−1, m−1) and becomes R_{e−1} = S S (S X_e) R_e, so R_e = Ch(e+1, m−1)
for 2 ≤ e ≤ m−2. At Φ(2, R_2) the chain Ch(2, 2) = T_2 needs no W step; E gives [X_2, R_2, S S (S X_2) R_2, S X_1 T_2 R_2],
and B (with R = R_2) reaches [X_m, S S (S X_m), T_m] with X_m = S S (S X_1)(S S (S X_2) Ch(3, m−1)) = Ch(1, m−1). Nothing
below the current top items is ever read, so the step from E_{m−1} to E_m holds whatever lies below. Counting: 1 + Σ_{e=3}^{m−2}
2e + 3 + 10 = m² − 3m + 10 steps; the opcodes are those listed for the lemmas, which gives the epoch word. The base of the
induction (the run reaches E_3, and X_2 = Ch(1, 1), X_3 = Ch(1, 2)) is checked on the concrete run. ∎
*Checks (code/countdown_proof.py, in verify_all).* The three lemmas and B; on the concrete run, X_e = Ch(1, e−1) for
e = 2..26 and the epoch-start form for every epoch; the opcode word predicted by the composition equals the concrete run
from E_3 to E_26 (5,382 steps). Whole list: each epoch run from [X_{m−1}, S S (S X_{m−1}), T_{m−1}] with junk below leaves
explicit pushes P(m) above the junk (they are the explicit outputs of W, E, O, B), so the list at E_m is
top(m) ++ P(m) ++ ⋯ ++ P(4) ++ (the concrete list below the top three at E_3); the first 30 entries agree with the
concrete run at 23/23 epoch starts. Hence R″_{k,d} holds for t_c for every k, d.
*Consequence.* Census counters with an exact proof: 148 of 152 at this point; two more by Theorem CD2 below (150 of 152).

## Two growing-opcode countdown runs, exact (Theorem CD2) (main agent, 2026-10-26)
*Setting.* t = S(SS)S(S(S(SS(SS))S))S and t′ = S(SS)S(S(S(SSSS)S))S, census counters whose opcodes grow without bound.
Levels: a_0 (a fixed term of each run: S(S(SS(SS))S)(S(S(S(SS(SS))S)))S for t, S(S(SSSS)S)(S(S(S(SSSS)S)))S for t′),
a_{k+1} = S S (S a_k)(S (S a_k)), b_k = S (S a_k); return form R(Z) = [Z, S (S Z), S S (S Z)(S (S Z))]; frame lists
Y⟨k⟩ = Y f_{k−1} ⋯ f_0 with f_j = S a_j b_j (Y f_{k−1} ⋯ f_{j+1}) (each frame points at the part of the list before it);
E(i, m) = (S a_i b_i a_{m+1})⟨m+1⟩ and E_m = E(m−1, m).
*Theorem CD2 — PROVED (symbolic lemmas checked by code/countdown2_call.py and code/countdown2_proof.py; composition by
hand; transient concrete).* For both terms and every m ≥ 3 the run passes through R(E_m), and R(E_m) → R(E_{m+1}) takes
6m² + (2B + 7)m + B + 8 steps (B = 20 for t, 22 for t′: 6m² + 47m + 28 and 6m² + 51m + 30) with an explicit opcode word.
*Lemmas.* CALL: [a_k, X, Y] ++ r →^{4k+B} R(Y⟨k⟩) ++ … ++ r, by induction from DL [a_k, X, Y] ++ r →⁴ [a_{k−1}, X′, Y X′,
X Y] ++ r with X′ = S a_{k−1} b_{k−1} Y (opcodes 3011; generic, a_{k−1} opaque) and BASE [a_0, X, Y] ++ r →^B R(Y) ++ … ++ r
(per term; X, Y opaque). TA: opening Z = S P Q W_1 ⋯ W_p in R(Z) puts [P, Q, W_1, …, W_p] on top. TB: R(a_{k+1} W_1 ⋯ W_p)
(p ≥ 1) →⁴ [a_k, X, W_1 X, W_2, …] with X = S a_k b_k W_1 (opcodes (3+p)011); TB0: R(a_{k+1}) →⁴ [a_k, X, a_{k+2} X, …]
with X = S a_k b_k a_{k+2} (because S S (S a_{k+1})(S (S a_{k+1})) = a_{k+2}). All with junk below, never read.
*Composition.* For 1 ≤ i ≤ m−1: R(E(i, m)) →TA→ [a_i, b_i, a_{m+1}, …] →CALL→ R(a_{m+1}⟨i⟩) →TB→ call of a_m with
X = S a_m b_m g, Y = g X, where g = S a_{i−1} b_{i−1} a_{m+1} →CALL→ R(Y⟨m⟩) = R(g⟨m+1⟩) = R(E(i−1, m)) (the frame X is g⟨m+1⟩'s
level-m frame, and the later frames coincide by definition); 4i + 4m + 2B + 5 steps. Final phase: R(E(0, m)) →TA, CALL(a_0)→
R(a_{m+1}) →TB0, CALL(a_m)→ R(a_{m+2}⟨m+1⟩) →TB, CALL(a_{m+1})→ R((S a_m b_m a_{m+2})⟨m+2⟩) = R(E_{m+1}); 8m + 3B + 13 steps.
Every lemma reads only the top return form and the spine just opened, so nothing below is read and the step holds whatever
lies below. Summing gives the epoch length. ∎
*Checks.* DL, BASE, TB, TB0 symbolic; the concrete runs reach R(E_3) (steps 307 and 330); the composed opcode words equal
the concrete runs from R(E_3) to R(E_14), resp. R(E_13) (9,328 and 7,995 steps), epoch by epoch; whole list (first 30
entries) at 11/11 and 10/10 epoch starts; the level-call lemma alone also at 14/14 epochs of t. The opcode words are nested
countdowns with affine counts (R″_PUP by Lemma PUP); the window words are determined for every k.
*Consequence.* Census counters with an exact proof: 150 of 152 (with Theorem CD). Left: S(SS)S(S(S(S(SSS))S))S (its widest
elements do not have this closed form) and the 'no scheme' counter.

## The last countdown run, exact (Theorem CD3) (main agent, 2026-10-26)
*Theorem CD3 — PROVED (symbolic lemmas and checks: code/countdown3_proof.py; composition as in Theorem CD2).* For
t = S(SS)S(S(S(S(SSS))S))S, with levels L_0 = S(SS)(S(SS)(S(SS)))(S(S(S(S(SSS))S))S), L_{k+1} = G(L_k) = S (S (S L_k)) (S L_k (S (S L_k))),
d_k = S (S L_k), return form R′(Z) = [Z, G(Z), S Z (S (S Z)) G(Z)], frame lists Y⟨k⟩ (f_j = S L_j d_j (prefix)) and
E(i, m) = (S L_i d_i L_{m+1})⟨m+1⟩, E_m = E(m−1, m): the run passes through R′(E_m) for every m ≥ 3 and R′(E_m) → R′(E_{m+1})
takes 4.5m² + 42.5m + 44 steps. *Lemmas:* DL′ [L_k, X, Y] →³ [L_{k−1}, X′, Y X′, X Y] with X′ = S L_{k−1} d_{k−1} Y (opcodes
211), BASE [L_0, X, Y] →^17 R′(Y), hence CALL [L_k, X, Y] →^{3k+17} R′(Y⟨k⟩); TB′ R′(L_{k+1} W_1 ⋯ W_p) (p ≥ 1) →³ [L_k, X,
W_1 X, W_2, …] with X = S L_k d_k W_1; TB0′ R′(L_{k+1}) →³ [L_k, X, W X, …] with W = S L_{k+1} d_{k+1} L_{k+2},
X = S L_k d_k W. *Composition:* phases i = m−1, …, 1 exactly as in CD2 (R′(E(i, m)) → R′(E(i−1, m)), 3i + 3m + 38 steps);
final phase R′(E(0, m)) →TA, CALL(L_0)→ R′(L_{m+1}) →TB0′, CALL(L_m)→ R′(W⟨m+1⟩) →TA, CALL(L_{m+1})→ R′(L_{m+2}⟨m+1⟩)
→TB′, CALL(L_{m+1})→ R′((S L_m d_m L_{m+2})⟨m+2⟩) = R′(E_{m+1}) (9m + 82 steps); each identification of a frame list uses
only the definition of the frames, as in CD2. *Checks:* the four lemmas symbolic; R′(E_3) reached at step 368; the
composed opcode word equals the concrete run over 5,328 steps (epochs 3–12); whole list (30 entries) at 9/9 epoch starts.
*Consequence.* With Theorems CD and CD2, every countdown counter of the 12-leaf census is proved exact: census counters
151 of 152; only the 'no scheme' counter SSS(S(S(SS)(SS)(SS)))S is left.

## The 'no scheme' counter, exact (Theorem NS) — every census counter is now proved (main agent, 2026-10-26)
*Setting.* t = SSS(S(S(SS)(SS)(SS)))S, the last census counter without an exact proof (the call prover found its level
families but 'no scheme': the return form changes from family to family). D = SS; layers [Y|C] := S S (S Y) C;
U(C) := S S (S C)(S S (S S D)(S C)); two fixed terms Q_1, Q_2 of the run (code/noscheme_proof.py); tops T_0 = Q_1,
T_g = Ch_g(B_g) with base members B_g = S S (S S D)(S T_{g−1}) and chains Ch_g(Z) = [Q_2|[Q_1|[T_1|⋯[T_{g−1}|Z]⋯]]] (each top
is a chain through all earlier tops); return forms R_g(Y) = [Y, S T_{g−1} Y, U(Ch_g(Y))]; driver states Δ_g = R_g(B_g).
*Theorem NS — PROVED (local lemmas checked symbolically by code/noscheme_proof.py; induction by hand; transient concrete).*
The run passes through Δ_g for every g ≥ 1 (Δ_1 at step 57), and Δ_g → Δ_{g+1} takes exactly 44·2^g − 4g − 14 steps.
*Lemmas (opaque atoms, unknown rest below never read):* E [B, X, Y] →³ [T, Y, S S D (S T) Y, X Y] for B = S S (S S D)(S T);
W [S, S Y, [Y′|C], P] →² [S, S Y′, C, P, …] (one chain layer); Wb [S, S Y, B, P] →⁴ [T, P, S S D (S T) P, …];
C1 [S S D (S T) Q, b, c] →³ [T, Q, [T|Q], …]; C2 [[T|Q], b, c] →² [Q, S T Q, c, …]; B0 [Q_1, P, Q] →^30 [Q, *, U([Q_2|Q])].
*Proof.* (1) Enter(k, P, Q) := [T_k, P, Q] ++ r reaches R_k(Q) ++ r′ in e_k steps, e_0 = 30, e_k = 2e_{k−1} + 2k + 10: for k = 0
this is B0 (R_0(Q) := [Q, *, U([Q_2|Q])]); for k ≥ 1, opening T_k = [Q_2|⋯] and k applications of W walk its layers Q_2, Q_1,
T_1, …, T_{k−1} down to B_k, and Wb gives Enter(k−1, Q, S S D (S T_{k−1}) Q); by induction this returns
R_{k−1}(S S D (S T_{k−1}) Q), whose front C1 opens into Enter(k−1, Q, [T_{k−1}|Q]); that returns R_{k−1}([T_{k−1}|Q]), and C2
gives [Q, S T_{k−1} Q, U(Ch_{k−1}([T_{k−1}|Q]))] = R_k(Q), because Ch_{k−1}([T_{k−1}|Q]) = Ch_k(Q) by the definition of the
chains (C1 and C2 use only the first and third elements of a return form). (2) A base call [B_g, X, Y] reaches R_g(Y): E gives
Enter(g−1, Y, S S D (S T_{g−1}) Y), then as in (1) (C1, a second Enter(g−1), C2). (3) The driver: Δ_g = [B_g, S T_{g−1} B_g,
U(T_g)] and U(T_g) = S S (S T_g)(S S (S S D)(S T_g)) = [T_g|B_{g+1}], so Δ_g is a base call of family g with Y = [T_g|B_{g+1}];
by (2) it reaches R_g([T_g|B_{g+1}]), and C2 gives [B_{g+1}, S T_g B_{g+1}, U(Ch_g([T_g|B_{g+1}]))] = R_{g+1}(B_{g+1}) = Δ_{g+1}
(again Ch_g([T_g|B_{g+1}]) = Ch_{g+1}(B_{g+1}) = T_{g+1}). Nothing below the current top is ever read. Solving the recursions:
e_k = 44·2^k − 2k − 14 and Δ_g → Δ_{g+1} in 2e_{g−1} + 10 = 44·2^g − 4g − 14 steps. ∎
*Checks.* The six lemmas symbolic; Δ_1 reached at step 57 and every Δ_g (g ≤ 10) at the predicted step; the composed opcode
word equals the concrete run from Δ_1 to Δ_10 (44,662 steps); whole list (first 30 entries) at 9/9 driver states. The run is
a binary recursion (time doubling per level, as observed in E71) over chain levels; its opcode word is built by a
two-call recursion with affine walk lengths — R″_PUP holds (and the window words are determined for every k).
*Consequence.* **Every one of the 152 counter-type head runs of the 12-leaf census is now proved exact** (call prover 147,
Theorems CD, CD2 (2), CD3, NS), together with the 150-term census sample and all 850 random-hunt endpoints (13–640 leaves).
These are per-term certificates; Conjecture R″_PUP for all terms remains open.

## Order-independent infinite evolution: a term with a unique redex forever (Theorem UR) (main agent, 2026-10-26)
*Observation.* If every list element of t = S e_1 ⋯ e_n is a normal form, the head redex is the only redex of t. A head
step [a, b, c] ++ R ⇒ spine(a) ++ [c, b·c] ++ R creates one new element, b·c; when a, b, c are normal forms, the
elements of spine(a) are normal forms, and b·c is a normal form iff b is S or S z (then b·c is S applied to at most two
normal forms). So t has exactly one redex at every step as long as its elements start normal and the second element is
always S or S z.
*Theorem UR — PROVED (hand proof; checked on 300,000 steps by code/unique_redex_t0.py).* t_0 = S(SSS)S(S(SSS)S) (10
leaves) has no normal form and has exactly one redex at every step of its evolution. Hence its multiway graph is a single
infinite path: every evaluation order — leftmost-outermost, leftmost-innermost, parallel (all redexes at once), or any
other strategy — produces the same infinite evolution, its head run.
*Proof.* Let A = SSS and B = S A S (normal forms), and let C be the least set of terms with SB ∈ C and S p (S q) ∈ C for
p, q ∈ C; its members are normal forms. Write Φ(c; R) = [c, Sc, Sc] ++ R.
(G) [A, S, c] ++ R → [S, S, c, Sc] ++ R → [c, Sc, Sc] ++ R = Φ(c; R); second elements S, S.
(H) [B, x, y] ++ R → [A, S, y, x·y] ++ R →(G) Φ(y; [x·y] ++ R); second elements x, S, S.
(D) If p = S p′ (S q′) then [p, S q, Sc] ++ R → [p′, S q′, Sc, S q·Sc] ++ R; second element S q.
Claim: from Φ(c; R) with c ∈ C ∪ {B} the run reaches some Φ(c′; R′) with c′ ∈ C, every step on the way having second
element S or S z. Case c = B: Φ(B; R) = [B, SB, SB] ++ R →(H, x = SB) Φ(SB; …), and SB ∈ C. Case c = SB: Φ(SB; R) →
[B, S(SB), S(SB)·S(SB)] ++ R (second element S(SB)) →(H, x = S(SB)) Φ(S c (S c); …), and S c (S c) ∈ C. Case
c = S p (S q) with p, q ∈ C: Φ(c; R) → [p, S q, Sc, Sc·Sc] ++ R (second element Sc). Put p_0 = p, q_0 = q; while
p_i ≠ SB we have p_i = S p_{i+1} (S q_{i+1}) with p_{i+1}, q_{i+1} ∈ C, and (D) moves from [p_i, S q_i, Sc] ++ … to
[p_{i+1}, S q_{i+1}, Sc] ++ …; p_{i+1} is a proper subterm of p_i, so some p_m = SB, and [SB, S q_m, Sc] ++ … →
[B, Sc, S q_m·Sc] ++ … (second element S q_m) →(H, x = Sc) Φ(S q_m (S c); …), and S q_m (S c) ∈ C.
Now the list of t_0 is [A, S, B] →(G) Φ(B; []). By the claim and induction the run passes through infinitely many
Φ-states (each with at least three elements), so it never reaches a head normal form, and at every step the second
element is S or S z. The initial elements A, S, B are normal forms, so by the observation every element ever created is a
normal form and the head redex is the only redex at every step. ∎
*Minimality and frequency (COMPUTATIONALLY CERTIFIED, code/unique_redex.py).* No term with at most 9 leaves keeps a unique
redex: each one with an infinite evolution creates a second redex within 5,000 steps. With 10, 11, 12 leaves, 2, 3 and 10
terms keep a unique redex for 5,000 steps (all of the same linear-counter kind; t_0 and S(S(SSS))(S(SSS))S at 10 leaves);
S(S(SSS)S)S(S(S(S(SSS)S)S)) keeps it for 2,000,000 steps. Only t_0 is proved for all time.
*Meaning for the prize.* For such terms the evolution order is irrelevant: Wolfram's weak definition (some order) and
strong definition (the multiway system) see the same single path. A universality construction built only from
unique-redex terms would therefore work in every sense; conversely, unique-redex runs are head runs, so they fall under the
leftmost-outermost analysis (R″_PUP). t_0 itself is a linear counter (call prover: call step '2 [call −1]', driver
'[call +1]', whole-list certificate), so it computes nothing complex.

## Leftmost-innermost (call-by-value) evolution (main agent, 2026-10-26)
*Facts — PROVED.* (i) S never erases an argument, so weak and strong normalisation coincide for S-terms (λI-style
conservation; consistent with Theorem T): an argument without a normal form keeps having none. Hence once the leftmost-
innermost (LI) evolution steps inside an argument without a normal form, it never leaves it, and the part of the term
outside that argument is frozen for ever. (ii) LI on S a_1 ⋯ a_n evaluates the first of a_1, a_2, a_3 that contains a
redex (to a normal form, or for ever), and contracts the head only when a_1, a_2, a_3 are normal forms. So an infinite LI
evolution either descends for ever (the frozen depth tends to infinity) or contracts at a fixed depth infinitely often
while every argument that reaches the first three positions normalises.
*Both cases occur.* Descent: all 43 terms with at most 8 leaves that have no normal form descend for ever in the
experiment (code/li_explore.py; frozen depth growing roughly linearly; normal forms inside grow, e.g. linearly for
S(SSS)S(SSS), exponentially for the binary counter SSS(SS)S(SS(SS)), whose LI evolution is not a counter at all).
Fixed depth: by Theorem UR, t_0's LI evolution is its head run, contracting at the root for ever; among the head runs of
code/robust_scan.py, S(S(SSS)S)S(S(S(S(SSS)S)S)) keeps its first three elements normal for 200,000 steps
(code/cbv_robust.py) and all others fail within 20 steps. Fixed depth also occurs *with* argument evaluation, already
at 9 leaves: S(S(SSS))(SS)(SS) — 5,786 of its first 6,000 LI steps contract the root, the rest are two-step
normalisations (S S (SS) X → S X (S S X)) at depth ≤ 3 whose spacing grows by one each time (a linear counter with
evaluated arguments; code/cbv_root.py, the root machine with a memoised normaliser, finds it as the only such term up
to 9 leaves; EXPERIMENTALLY SUPPORTED, no proof for all time). Counts of terms whose root keeps contracting for 2,000
contractions: 1, 13, 40 with 9, 10, 11 leaves, most of them evaluating arguments on the way (E81).
*Consequence for detectors.* In the descent case a detector that reads a bounded prefix of the term (written head first)
sees a prefix that is eventually frozen, and whether the evolution enters a non-normalising argument is decidable at each
level (normalisation is decidable), so such detectors are decidable on descending LI evolutions; the fixed-depth case is a
head-run-like machine on normal forms (its arguments are evaluated before each contraction) and needs its own analysis.
Not proved: which terms descend; whether the fixed-depth case always reduces to robust head runs.

## The multiway graph of an S-term: potential, acyclicity, directedness (Proposition MW) (main agent, 2026-10-26)
For a term t let |t| be its number of leaves and D(t) the sum of the depths of its leaves.
*Proposition MW — PROVED (parts (a)–(c) and (e) elementary; (d) uses the cited cofinality theorem).*
*MACHINE-CHECKED (lean/MW.lean, 2026-10-27): (a) `red_potential` and (b) `acyclic`, `unbounded`, for one-redex steps
anywhere in the term (so for every evolution order and every choice of redexes; a parallel step is a finite sequence of
such steps). `unbounded`: for every infinite evolution s and every N some s n has more than N leaves. Standard axioms.*
*MACHINE-CHECKED (lean/Confluence.lean, 2026-10-27): confluence of S-reduction (`confluence`, by parallel reduction and
Takahashi's complete development; this is fact F2 used in (d)), uniqueness of normal forms (`nf_unique`), and (e)
(`mw_e`, `mw_e_terminal`, for any decoder into any system M whose reachability is transitive). Axiom: propext only.
Not formalised: the cofinality of Gross–Knuth reduction used in the second half of (d).*
(a) *Potential.* If t → u contracts a redex S x y z anywhere in t, then |u| = |t| + |z| − 1, and if z = S then
D(u) = D(t) − |x|. So (|t|, −D(t)) increases strictly (lexicographically) along every step, in every evolution order.
*Proof.* The context is unchanged, so compare B = ((S x) y) z with A = (x z)(y z) at the redex depth d. Leaves:
|B| = 1 + |x| + |y| + |z|, |A| = |x| + |y| + 2|z|. Depths for z = S: in B the head S is at d + 3, the leaves of x at
d + 3 + (depth in x), those of y at d + 2 + …, z at d + 1; in A the leaves of x are at d + 2 + …, those of y at d + 2 + …,
and the two copies of z at d + 2. The difference is −|x| (x moves up one level) − (d + 3) (head removed)
+ 2(d + 2) − (d + 1) (z) = −|x|. ∎ (Machine-checked on all 39,562 one-step reductions of the terms with ≤ 11 leaves and of
3,000 random terms with 13–60 leaves: code/multiway_check.py, 0 violations.)
(b) *Acyclicity; sizes diverge.* No S-term reduces to itself in one or more steps, so the multiway graph of every term is
a DAG; and along every infinite evolution (any order, any choice of redexes, sequential or parallel) |t_n| → ∞.
*Proof.* The potential of (a) strictly increases. If the sizes along an infinite evolution were bounded by N, all its terms
would lie in the finite set of terms with ≤ N leaves, on which the potential takes finitely many values — impossible for
a strictly increasing sequence; and sizes never decrease. ∎
(c) *Reachability is decidable.* Every reduction path from t to u stays inside the finite set of terms with ≤ |u| leaves
(sizes never decrease), so a search of that set decides whether u is a reduct of t.
(d) *Directedness.* Any finitely many reducts of t have a common reduct (confluence, F2). With the cited fact that
Gross–Knuth reduction (contract all redexes at once, as a complete development) is cofinal in orthogonal systems (Terese,
'Term Rewriting Systems', 2003, ch. 4; Klop 1992): for every property P closed under reduction (u ⊨ P, u →* v ⇒ v ⊨ P),
'some state of the multiway system satisfies P' holds iff the single Gross–Knuth evolution of t eventually satisfies P.
So multiway detectors of that kind are no stronger than one deterministic evolution; Böhm-tree properties (F5) and
'size ≥ N' are examples of reduction-closed properties.
(e) *Branching of the emulated machine cannot be mirrored by branching of S.* Suppose a strong-sense emulation decodes the
states reachable from enc(c) into configurations of a multiway system M with a decoder Dec that respects reachability
(u →* v ⇒ Dec(u) →*_M Dec(v)) and is defined on a cofinal set of reachable states. Then any two decoded configurations
have a common M-descendant; so if M reaches two distinct terminal configurations from c (e.g. an accepting and a
rejecting halt of a nondeterministic machine), no such emulation exists. *Proof.* Reachable u_1, u_2 decoding to the two
terminal configurations have a common reduct w (d), which reduces to a decodable w′; Dec(w′) is reachable from both
terminal configurations, so equals both. ∎
*Scope.* (e) applies verbatim to every confluent system, SK combinator logic included; so Wolfram's strong definition, if
it is to make SK universal, cannot ask S's branching to mirror nondeterministic branching. A strong-sense emulation must
represent the emulated machine's branches as data inside the evolving terms and read the result through a property of the
multiway system — for reduction-closed properties that is, by (d), a property of the single Gross–Knuth evolution, which
falls under gap (4) of the gap map (intermediate syntax under a non-leftmost order) unless it is a Böhm-tree property
(gap (2)). Proposition MW does not decide either gap.

## Lazy parallel evaluation (Lemma LZ) and an exact parallel loop (Theorem PL) (main agent, 2026-10-26)
*Lemma LZ — PROVED (from the definition of a ReplaceAll pass P; implementation code/lazy_par.py checked against direct
passes on 14 terms, every pass the direct method reached, E96).* For every term t = S a_1 ⋯ a_m:
(i) if m ≥ 3, P(t) = a_1 a_3 (a_2 a_3) P(a_4) ⋯ P(a_m) (Lemma PH); (ii) if m ≤ 2, P(t) = S P(a_1) ⋯ P(a_m).
*Proof of (ii).* (S a_1) a_2 is not a redex (S a_1 is not of the form S x y), so a pass recurses into function and
argument: P(S a_1 a_2) = P(S a_1) P(a_2) = S P(a_1) P(a_2), and likewise for m ≤ 1. ∎
*The lazy machine.* Keep the list of t as entries (x, b), meaning the element P^(now−b)(x). A pass takes the first three
entries, forms their current values v_1, v_2, v_3, and replaces them by spine(v_1) ++ [v_3, v_2·v_3], stamped now+1; the
entries below are not touched, and by (i) they have aged by one pass. The spine of v_1 = P^w(x) comes from w passes of x's
own lazy run (recursively; memoised by (x, w)). Once that run has fewer than three elements, the remaining passes only age
its elements, by (ii). So the parallel run's opcode word (spine length of the element opened at each pass) is computed
exactly, evolving only what the head opens.
*Symbolic use.* Allow atoms of two kinds. A *normal atom* stands for a normal form, and no pass changes it. A *general
atom* stands for an arbitrary term; it ages and may never be opened. If a run of the machine opens no atom-headed element
and never reads the designated unknown rest, it holds for every instantiation: (i) and (ii) hold for all terms, and
hash-consing only identifies equal symbolic terms, whose instances are equal.
*Remark.* This makes Lemma PH's remark (3) exact. A parallel run is a head run in which each opened element is first
evolved for as long as it waited — a hierarchy of nested evolutions, of which the machine computes only the parts that
reach a head.

*Theorem PL — PROVED (symbolic lemmas checked by code/par_loop_proof.py on the lazy machine; composition by hand;
transient concrete).* Let t = S(S(S(S(SSS)(SSS))))SS, D = S(SS), L = S D, C_1 = L, C_{i+1} = L C_i (normal forms: L has
one argument and L C two, all normal), and
  Σ_j = [D, L, C_j, C_{j−1}(C_2 C_j)],   Λ_i = [D, C_i, C_{j+1}, C_j (C_{i+1} C_{j+1})]  (within cycle j; Λ_1 = Σ_{j+1}).
The parallel (ReplaceAll) evolution of t passes through Σ_j (as its first four list elements) for every j ≥ 4 — Σ_4 at
pass 21, and Σ_j → Σ_{j+1} in 12 + 8(j − 3) passes. Its opcode word is u ∏_{j≥4} 110311031104 (11031104)^{j−3}, where u
is the first 21 opcodes: one growing loop, so it is morphic and R″_PUP holds for it.
*Lemmas* (U, V, W normal atoms; the rest r consists of general atoms and is never read):
(I) Σ_j ++ r →^12 Λ_{j−2} ++ r′ with C_{j−2} = W (j ≥ 3; opcodes 110311031104);
(II) Λ_i ++ r →^8 Λ_{i−1} ++ r′ with C_{i−1} = U and C_j = V (i ≥ 2; opcodes 11031104).
*Proof.* By (I), then (II) for i = j−2, …, 2, Σ_j reaches Λ_1 = Σ_{j+1} in 12 + 8(j − 3) passes. Only the first four
elements are read, so this holds whatever lies below. The concrete run is at Σ_4 at pass 21; induction on j. ∎
*Checks.* Both lemmas pass symbolically. The concrete run is at Σ_j at the predicted pass for j = 4..60 and j = 160, and
the predicted word equals the concrete parallel word for 100,000 passes. The fourth element of Σ_j and Λ_i is not a normal
form (C_{j−1}(C_2 C_j) is a redex). It ages while waiting, but the lemmas only move it, never open it, so it is never
evolved.
*Meaning.* This is the first exact parallel run of a term whose parallel and head runs differ (Theorem CA-par, K0 and
Theorem UR concern runs that coincide with their head runs). Here the parallel run is *simpler* than the head run (one loop
against the head run's nested loop): the waiting element SSS(S(SS)) becomes the normal form C_2 one pass after it starts
waiting, before the head reaches it. All 150 parallel runs of the census sample look loop-like for 20,000 passes (E96).
The same method (lazy machine + symbolic normal atoms) should prove them term by term, but it is not automated. Gap (4)
is not closed by per-term certificates either.

## Parallel loop runs, automatically (Theorem LP-par) (main agent, 2026-10-26)
*Method.* Theorem LP's prover (code/loop_prover.py) with its head engine replaced by the parallel engine of Lemma LZ. A
step opens the first element and builds spine(a) ++ [c, b·c], and every element below the consumed three ages by one
pass. The cycle-start windows are read off the lazy parallel run. Two variants, both sound:
* code/par_loop_prover.py (*values*): snapshots are the elements' values (all pending passes carried out). A pending pass
  inside a pattern is a node P^k(p), forced when opened. Canonical, but a window element containing a sub-term that keeps
  evolving has an ever larger value, and those terms fail ("value too large").
* code/par_loop_prover2.py (*lazy representation*): a pending pass is written DK_k·x, an application of a special atom,
  so the loop prover's anti-unification and comb families work unchanged. Snapshots and engine use one canonical aging
  rule, a function of (x, k) only, so aging pass by pass agrees with aging once by the total:
  age(x, k) = x if x is certainly normal; S age(a, k) age(b, k) if x = S a b (Lemma LZ (ii)); for an active x (or
  x = DK_j·y, with k := j + k), its normal form if min(k, 8) passes reach one, else DK_k·x.
*Theorem LP-par — PROVED per certified term (lemmas checked on the parallel engine; computer-assisted).* If either
variant certifies a term, its parallel evolution is forever the certified cycle: from the cycle-start window W(n) it
reaches M(n) and then M(n+1) in α·n + β passes, so its parallel opcode word is u ∏_n u_0 B_1^(n+b_1) u_1 ⋯ (morphic).
*Soundness.* (1) Lemma LZ's identities hold for all terms. If P^m(x) is a normal form then P^k(x) is the same normal form
for every k ≥ m. Normal forms are fixed points of P. A pending pass that cannot be resolved symbolically is kept, and it
is still exact. (2) Atoms OPQ/VAR are treated as normal forms. A loop (block lemma A(F(O)) →^L A(O)) is accepted only
for a normal comb family (X normal; F normal with its hole never applied), so every instance of O is a normal form. An
element of A that a block leaves untouched ages during it, so the block lemma's comparison holds only if that element is
normal. (3) Nothing below a window is read (junk check), so aging of the rest is irrelevant. (4) Patterns are compared
syntactically; equal representations denote equal terms, so a mismatch can only make the prover fail. (5) The whole-list
(residue) pass would have to age pushed segments, and it is not implemented. These certificates describe the opcode word
and the windows, not the whole list. Independent numerical cross-check as in Theorem LP: at every later cycle start the
concrete lazy state is an instance of M(n) and M(n+1).
*Extension (code/par_loop_prover3.py) — loops over evolving comb families.* Two changes to the lazy-representation
variant. (1) A loop whose comb family is not normal is accepted when its block lemma A(F(O)) →^L A(O) also holds with O
(and the loop variable) treated as a *general* atom: every element containing O that waits is aged exactly (pending-pass
node), and O may never be opened. A lemma that passes then holds for every instance of O, normal or not, so
A(F^m(X)) →^{mL} A(X) by induction for any X. Loop windows may also write out ℓ ≤ 2 comb layers above the variable
(lookahead), which leaves a valid block lemma A(F(O)) → A(O) with n + b − ℓ blocks. (2) The settle check of the aging rule
(min(k, 8) passes of an active element) may not unfold a comb token; if it would, the pass stays pending, which is exact.
Without (2), forcing an element whose comb layers keep evolving unfolded the comb level after level. With (1) and (2),
S(S(S(SS))S)(SSS)(SS) is certified (cycle 5n + 20, cross-check 102/102), as is S(S(SS)SS)S(SS) (4n + 23, 113/113).
Soundness is unchanged in kind: every representation the engine produces denotes the term exactly, every accepted lemma
holds for all instances of its atoms, and a disagreement between representations can only make a comparison fail.
*Coverage (E98, E100).* On the 150-term census sample, **86 parallel runs are certified exact**: comb runs 21/22, loop
runs 35/63, counter-type runs 30/65 (head runs certified by the call prover; these parallel runs are plain loops). Per
variant: values 44 loop/comb; lazy 43 loop/comb + 5 counters; the extension 48 of those 49 + 12 loop/comb + 25 counters.
Every certificate's cycle structure was checked against the concrete lazy parallel word for 400,000 passes
(code/par_cert_check.py): every cycle word is the previous one with at most m chunks inserted. *Correction:* an earlier
version of this paragraph said that in S(S(S(SS))S)(SSS)(SS) "opening the top element forces every layer". That was wrong.
The deep unfolding came from the prover's own settle check (forcing up to 8 passes of elements that never settle), not
from the run. Forcing the opened element needs only two passes, and with the restricted settle check the term is
certified. *Not certified (64):* 40 time out (240–300 s), 17 fail on token unfolding, 4 find no comb pattern, 3 have no
growing-loop cycle. The open cases include the binary-type counters, whose parallel runs would need a parallel call
prover.

## Unique-redex terms classified up to 17 leaves (Theorems UR-Φ, UR-Φ-II) (main agent, 2026-10-26)
*Setting.* Lists of normal forms with the head machine [a, b, c] ++ R ⇒ spine(a) ++ [c, b·c] ++ R. By the observation
of Theorem UR, the head redex is the only redex of the term for as long as every list has ≥ 3 elements and its second
element has spine ≤ 1. Write Φ(c) = [c, S c, S c], and call a normal form *of form ⊗* if it is S p (S q) (p, q normal).
A *base* is a normal form not of form ⊗. For c = S p (S q), the *walk* is p_0 = p, q_0 = q, p_i = S p_{i+1} (S q_{i+1})
while p_i is of form ⊗; it ends at a base p_m. Write chain(c) = m and end(c) = q_m.
*Base lemmas.* A base β is of *type A* if for all normal forms x, y and lists R of normal forms
[β, S x, S y] ++ R →^{k_β} Φ(S x (S y)) ++ R′ (second element of spine ≤ 1 throughout, R never read), and of *type II* if
the same holds with Φ(S y (S (S y))) instead. These are checked symbolically with opaque x, y and junk R: x and y are
never opened and never stand alone as the second element, so every step is independent of them
(code/ur_phi_proof.py). S B with B = S(SSS)S is of type A (word 1220). S(S B S) and S(S B (SS)) are of type A (12220).
S(S(S B))S is of type II (211220).
*Theorem UR-Φ — PROVED.* Let 𝔅 be a set of type-A bases and C(𝔅) the least set containing 𝔅 and closed under
(p, q) ↦ S p (S q). For every c of form ⊗ in C(𝔅) and every list R of normal forms, the term with list Φ(c) ++ R has
exactly one redex at every step for ever. It passes through Φ(c_k) ++ R_k with c_0 = c and c_{k+1} = S e_k (S c_k),
where e_k = end(c_k), and its opcode word between Φ(c_k) and Φ(c_{k+1}) is 2·2^{chain(c_k)}·w_β, with β the base ending
c_k's walk.
*Proof.* Φ(c) = [S p (S q), S c, S c] ++ R → [p, S q, S c, (S c)(S c)] ++ R (opcode 2; second element S c). For i < m,
[p_i, S q_i, S c] ++ … → [p_{i+1}, S q_{i+1}, S c, (S q_i)(S c)] ++ … (opcode 2; second element S q_i). At the base,
[β, S q_m, S c] ++ … → Φ(S q_m (S c)) ++ … by β's lemma with x = q_m, y = c. The walk terminates because every p_i is a
proper subterm of c. Membership: c ∈ C(𝔅) of form ⊗ means p, q ∈ C(𝔅), and inductively every p_i, q_i ∈ C(𝔅), so
e = q_m ∈ C(𝔅) and S e (S c) ∈ C(𝔅). Induction on k. Every list element stays a normal form (b·c with b ∈ {S, S z}),
so the head redex is the only redex. ∎
*Corollary (structure).* Every such run is a linear counter. If e_k is not a base, then e_{k+1} = end(e_k) is a proper
subterm of e_k, so within |c| Φ-steps some e_k = β is a base. From then on, by the definitions,
c_{k+1} = S β (S c_k), e_{k+1} = c_k, c_{k+2} = S c_k (S c_{k+1}) and e_{k+2} = end(c_k) = e_k = β. So the Φ-steps
alternate between walk length 0 (base β) and walk length chain(c_k) + j, growing by one per pair (base β′ ending c_k's
walk). The opcode word is u ∏_j (2·w_β)(2·2^{L+j}·w_β′): morphic.
*Theorem UR-Φ-II — PROVED (same proof).* If β is of type II, then for every c of form ⊗ whose walk ends at β (q's
arbitrary normal forms), the run from Φ(c) ++ R has a unique redex for ever, with c_{k+1} = S c_k (S (S c_k)). This
element is again of form ⊗, its walk passes through c_k's and ends at β, and chain(c_{k+1}) = chain(c_k) + 1. Linear
counter.
*Classification up to 17 leaves — COMPUTATIONALLY CERTIFIED via the theorems.* code/unique_redex.py enumerates every
S-term with ≤ 17 leaves whose head redex is its only redex for 3,000 steps. There are 0 with ≤ 9 leaves, and 2, 3, 10,
26, 68 and 181 with 10, 11, 12, 13, 14 and 15 leaves: 290 terms. For each of them, code/ur_phi_proof.py checks the
concrete run (unique redex at every step) up to a Φ-state Φ(c) covered by a theorem. 286 are covered by Theorem UR-Φ and
4 by UR-Φ-II (S(SSS)S(S(S(S(S(SSS)S)))S), S(S(SSS))(S(S(S(S(SSS)S))))S, and the same with one more S). With 16
leaves there are 481 such terms, all covered (470 by UR-Φ, 11 by UR-Φ-II), and with 17 leaves 1,316, all covered (1,290
by UR-Φ, 26 by UR-Φ-II): 2,087 terms in all. So, up to 17 leaves, a term (whose head redex is its only redex) keeps a unique redex for 3,000 steps iff it keeps one for ever.
Every such term has a single-path multiway graph, the same evolution in every evaluation order, and that evolution is a
linear counter. (A head normal form whose unique redex lies in an argument evolves like that argument, but only until that
argument's own run descends again, and descents can recur for ever: see "Correction — descending one-redex evolutions"
after Theorem UR-C. This enumeration counts only terms whose head redex stays the only redex.) Every base met (44 distinct
ones) contains the gadget B = S(SSS)S.
*Lemma R (rounds) — PROVED.* In every infinite head run of an S-term, opcode 0 occurs infinitely often. Between two
consecutive opcode-0 steps, each opened element is the first spine argument of the one opened before it. *Proof.* After
[a, b, c] ++ R ⇒ spine(a) ++ [c, b·c] ++ R, the next element opened is a_1 (the first argument of a, a proper subterm of
a) if spine(a) ≠ [], and c if a = S. A strictly descending chain of subterms is finite. ∎ In a unique-redex run, opcode 0
needs second element S, so every round starts at [c, S c] ++ R and descends along c's left spine. Φ-states are the
rounds whose next element is S c again. This is the starting point for a classification at every size.
*Lemma R′ (the round machine) — PROVED.* Let a unique-redex run be at a round start [c, S c, d] ++ W. Let c = c_0,
c_1, …, c_r = S be c's left spine (c_{i+1} the first argument of c_i), each c_i (i < r) being S c_{i+1} (type 1) or
S c_{i+1} t_i (type 2). Start with (u, v) = (S c, d) and an empty push list P. For i = 0, …, r−1: at type 1,
(u, v) ← (v, u·v); at type 2, P ← [u·v] ++ P and (u, v) ← (t_i, v). The round keeps a unique redex iff u has spine ≤ 1
after every step and u = S at the end. The next round then starts at [v, S v] ++ P ++ W, and nothing in W is read during
the round. *Proof.* By induction on i, the list before step i is [c_i, u, v] ++ P ++ W. Type 1:
[S c_{i+1}, u, v] ++ … → [c_{i+1}, v, u·v] ++ …; type 2: [S c_{i+1} t_i, u, v] ++ … → [c_{i+1}, t_i, v, u·v] ++ …; end
(c_r = S, u = S): [S, S, v] ++ P ++ W → [v, S v] ++ P ++ W. The second element after each step is the new u. ∎ So a
unique-redex run is a two-register machine on rounds: each round reads only c and d and outputs c′ = v and d′ = head of
P (or of W if no type-2 step occurred). Φ-states are the rounds with d = S c, and Theorems UR-Φ/UR-Φ-II are the cases
where the walk's types are 2, …, 2 down to a base whose own walk returns Φ. Example: B = S A S walks
type 2 (t = S), type 2 (t = S), end, so it sends any (u, v) to c′ = v.
*Theorem UR-R (the Φ-regime, every size) — PROVED.* Let a head run have a unique redex at every step for ever, and number
its rounds from the first opcode-0 step (Lemma R′; round k starts at [c_k, S c_k, d_k] ++ W_k). Then:
(a) at most three rounds are not Φ-rounds (d_k ≠ S c_k), and every round after them is a Φ-round;
(b) the left spine of every Φ-element c ends with B = S(SSS)S, A = SSS, S, so every such run contains the gadget B;
(c) in a Φ-round with m type-1 steps, c_{k+1} = S c_k if m = 0 and c_{k+1} = S z_k (S^{m−1}(S c_k)) for some z_k if m ≥ 1;
(d) each type-1 step of a Φ-round except the last is preceded by a type-2 step with t = S;
(e) in the Φ-regime nothing below S c_k is ever read, so the run is a deterministic map c_k ↦ c_{k+1} = Ψ(c_k) on
normal forms, and the opcode word between Φ(c_k) and Φ(c_{k+1}) is the type word of c_k's left spine followed by 0.
*Proof.* (1) Endings. A round ends with u = S. After a type-2 step u = t; after a type-1 step u = old v. v starts as d_k,
and every type-1 step makes it an application. So either (E1) the last step is type 2 with t = S, or (E2) it is type 1
with old v = S, which needs d_k = S and makes it the round's only type-1 step. (The empty walk, c_k = S, ends with
u = S S: invalid.)
(2) Dying. If a round ends (E1) and the u before its last step is S z, then d_{k+1} = (S z) c_{k+1} has spine 2. In round
k+1 any type-1 step would set u to that spine-2 term, and c_{k+1} = S would end with u ≠ S; so all its steps are type 2,
c_{k+1} has spine 2 and c_{k+2} = S z c_{k+1}. Round k+2 then starts with a type-2 step whose t is c_{k+1}, of spine 2:
invalid.
(3) So in a run that never dies, every (E1) round has u = S before its last step, and d_{k+1} = S·c_{k+1}: its successor
is a Φ-round. A Φ-round has d_k = S c_k ≠ S, so by (1) it ends (E1); hence Φ-rounds follow Φ-rounds. The u = S before the
last step cannot come from a type-1 step (in a Φ-round v is never S) nor from u_0 = S c_k (walk of length ≥ 2), so the
second-to-last step is type 2 with t = S: c_{r−2} = S c_{r−1} S and c_{r−1} = S S S, i.e. c_{r−2} = B, c_{r−1} = A. That
is (b). A non-Φ round ending (E1) has a Φ successor. One ending (E2) has d_k = S. If it made a type-2 step, d_{k+1} is
an application and round k+1 ends (E1). If not, c_k = S S, and round k+1 (on c_{k+1} = S (S S) S) makes one. So at most
three non-Φ rounds occur: (a).
(4) Type-1 steps in a Φ-round. Let them be the 1st, …, m-th, with u^{(j)} the u just before the j-th, v_0 = S c_k and
v_j = u^{(j)}·v_{j−1}. The (j+1)-th type-1 step sets u = v_j, so spine(v_j) ≤ 1, i.e. u^{(j)} = S for j < m. That u
cannot be u_0 = S c_k nor come from a type-1 step (it would be some v_{j−2} ≠ S), so it is the t = S of the preceding
type-2 step: (d). Then v_{m−1} = S^{m−1}(S c_k) and c_{k+1} = v_m = u^{(m)}·S^{m−1}(S c_k), or S c_k if m = 0. If m ≥ 1
and u^{(m)} = S, then c_{k+1} = S·S^{m−1}(S c_k). The next round opens it with a type-1 step at u_0 ≠ S, giving v of
spine 2, and its very next step is again type 1 (S^{m−1}(S c_k) begins with S·): invalid. So u^{(m)} = S z_k: (c).
(5) In an (E1) round the last step pushes, so d_{k+1} is the last push and W_k is never read: (e). ∎
*Checks* (code/ur_regime_check.py): (a)–(d) hold on all 2,087 unique-redex runs up to 17 leaves (60 rounds each). The
m-values met are 0 (rare), 1 (most) and 2 (type II). Open, the last step to a classification at every size: show that Ψ's
orbits are always linear counters, i.e. that the pointer z_k (a t-component of c_k's walk, or S^i(S c_k)) always settles
into one of the patterns of Theorems UR-Φ and UR-Φ-II.
*Machine check of Theorem UR-R's core (Lean 4, lean/URCore.lean; plain Lean core, no Mathlib; every theorem depends
only on the standard axioms propext and Quot.sound, with no sorry; code/lean_check.py).* Terms, argument lists, the head machine
step [a, b, c] ++ R ⇒ args a ++ [c, b·c] ++ R, normal forms, and the unique-redex condition on lists (`good`: all elements
normal, second element with at most one argument; `urForever`: good at every step). Formally proved:
`end_lemma` (a final opcode-0 step stays good only if the second element is S); `step_nf`; `dying_lemma` (for all c, z, P:
[c, S c, S z c] ++ P is not unique-redex for ever); `phi_successor` and `phi_successor_state` (from [A, u, v] ++ P a lasting
run has u = S and is at the Φ-state [v, S v, S v] ++ P two steps later); `walk_to_A`, `walk_gen`, `reach_round` (round
structure); **`reach_phi`** (every list that keeps a unique redex for ever reaches a Φ-state) and **`phi_next` /
`phi_forever`** (from a Φ-state, Φ-states recur for ever). So Theorem UR-R's statement that unique-redex runs enter the
Φ-regime and stay in it is machine-checked. The link between "the head redex is the term's only redex at every step"
and `urForever` is the Observation of Theorem UR (all elements normal and the created element b·c normal), proved by
hand and not yet formalised. **Update (2026-10-26, evening): Theorem UR-C is now formalised too** (below:
`ur_classification`, `ur_counter`; 19 theorems in the file, 0 errors, no sorry; the UR-C part uses the three standard
axioms propext, Classical.choice, Quot.sound).
*Theorem UR-C (classification of head-unique runs, every size) — PROVED (hand proof; every transition rule checked on
all 2,087 real unique-redex runs and on 29,366 sampled Φ-orbits, about 1.9 million transitions in all, code/ur_pointer_check.py)
and MACHINE-CHECKED in Lean 4 (lean/URCore.lean).*
Every S-term whose head redex is its only redex at every step for ever (its argument list satisfies `urForever`) is,
after finitely many rounds, one of two linear counters:
(A) the pointer alternates between a fixed *base* β (an element whose walk starts with a type-1 layer) and the previous
Φ-element: c_{k+1} = S c_{k−1} (S c_k) and c_{k+2} = S β (S c_{k+1}) for all k ≥ k_0 of one parity;
(II) c_{k+1} = S c_k (S (S c_k)) for all k ≥ k_0.
Its opcode word is u ∏_j (fixed blocks with one exponent growing by one per period), which is morphic. Its multiway
graph is a single path, so every evaluation order performs exactly this evolution. **Scope (corrected 2026-10-26,
evening):** an earlier version of this statement read "every S-term whose evolution has exactly one redex at every step"
and added that a unique redex inside an argument of a head normal form "reduces to this case". That is not what is
proved: a one-redex evolution can descend into arguments infinitely often (see the correction below).
*Notation.* By Theorem UR-R the run is eventually the map Ψ on Φ-elements. w(c) is the walk (left-spine layers 1 = S x,
(2, t) = S x t), m(c) its number of type-1 layers, and τ(c) its type word. The pointer z(c), for m ≥ 1, is given by
S z(c) = the u just before the last type-1 step, which has spine 1 by UR-R(c). It is "pred" (the inner part of the
preceding layer's t), "pos0" (c itself, when the last type-1 layer is the walk's first layer) or "cons" (S^{m−3}(S c),
or c if m = 2, when the last two type-1 layers are consecutive). Then Ψ(c) = S c if m = 0, and Ψ(c) = S z X with
X = S^{m−1}(S c) ≠ S otherwise. All rules below are necessary conditions in a run that keeps a unique redex for ever.
(P) [UR-R(c), (d)] Every type-1 layer except the last is preceded by (2, S). A type-1 layer at position 0 is the last
one (u_0 = S c ≠ S).
(W) w(c_{k+1}) = (1)·w(c_k) if m_k = 0, and (2, X_k)·w(z_k) if m_k ≥ 1.
(T0) m_k = 0 ⇒ round k+1 has a single type-1 layer, at position 0: m_{k+1} = 1, z_{k+1} = c_{k+1}.
(T1) m_k ≥ 1 and w(z_k) starts with a type-1 layer. That layer follows (2, X_k) with X_k ≠ S, so by (P) it is round
k+1's last type-1 layer: m_{k+1} = 1 and z_{k+1} = S^{m_k−2}(S c_k), or c_k if m_k = 1. If m_k ≥ 2, then
w(c_{k+2}) = (2, S c_{k+1})·(1)^{m_k−1}·w(c_k) has m_k − 1 + m_k ≥ 3 type-1 layers, the first after t ≠ S: by (P) the
run dies. So in a lasting run T1 happens only with m_k = 1, and z_{k+1} = c_k.
(T2) m_k ≥ 1 and w(z_k) starts with a type-2 layer (it is non-empty: z_k = S would end the round with u = X_k ≠ S).
The type-1 layers of w(c_{k+1}) are those of w(z_k), with the same predecessors. So m_{k+1} = m(z_k), and z_{k+1} is
"pred", the inner part of a t-component of z_k's walk and hence a proper subterm of z_k, or "cons", or m_{k+1} = 0.
(S) Consecutive "pred"-T2 steps strictly shrink the pointer, so a T0, T1 or "cons" step occurs within |z| rounds.
(II) A "cons" step with m = 2 makes z = c. Then w(c) starts with a type-2 layer (else T1 with m = 2 kills the run),
and T2 copies m = 2 and the consecutive pair. So the self pointer recurs: type II for ever. A "cons" step with m ≥ 3
makes z = S^{m−3}(S c), whose walk starts with a type-1 layer; that is T1 with m ≥ 2, and the run dies.
(A) T0 leads to "pos0" with m = 1 and then to a T1 step. Let round k be T1, so z_k = c_{k−1}, m_{k−1} = 1, and
β := z_{k−1} has a walk starting with a type-1 layer. Round k+1 has w(c_{k+1}) = (2, S c_k)·w(c_{k−1}). If w(c_{k−1})
starts with a type-2 layer, T2 inherits round k−1's predecessor: z_{k+1} = β, m = 1. Round k+2 has
w(c_{k+2}) = (2, S c_{k+1})·w(β), which is T1: z_{k+2} = c_{k+1}, with the same β. By induction the pointer
alternates β, c_{prev}, β, … for ever. If instead w(c_{k−1}) starts with a type-1 layer (c_{k−1} = S c_{k−2} after an
m = 0 round), one more T1 step occurs and the same induction starts a round later with β = c_{k−1}.
(Linear counter) In (A), |w(c)| is 1 + |w(β)| on one parity and 1 + |w(c_{prev})| on the other, growing by one per
two rounds. In (II) it grows by one per round. The opcode word between Φ(c_k) and Φ(c_{k+1}) is τ(c_k)·0 with
τ(c_{k+1}) = 2·τ(z_k), so it is u ∏_j (2 τ(β) 0)(2^{j+a} τ_0 0) in (A) and u ∏_j (2^{j+a} τ_0 0) in (II). ∎
*Corollary — the head-unique class at every size.* Combined with Theorem UR-R: every S-term whose head redex stays its
only redex for ever does so through a linear counter of type A or II, entered after finitely many steps, with the
gadget B = S(SSS)S at the bottom of every Φ-element. No such term computes anything beyond a linear counter, in any
evaluation order or in the multiway system. The enumerations (2,087 terms ≤ 17 leaves, E99) and Theorems
UR-Φ/UR-Φ-II are consistent instances. Machine-checked as `ur_counter` (lean/URCore.lean).
*Meaning.* With Theorems UR-R and UR-C this settles the head-unique class at every size and in every evaluation order:
head-unique S-terms compute nothing beyond linear counters. The wider class of all one-redex evolutions (where Wolfram's
weak and strong notions coincide trivially) also contains evolutions that descend into arguments for ever. Theorems
UR-R/UR-C do not cover those; Theorem DK below covers every one found up to 14 leaves.

*Correction — descending one-redex evolutions (2026-10-26, evening; E108).* A one-redex evolution can leave the
head-unique class without gaining a second redex. When the active list is exactly [S, S p q, c] (all normal), the head
step gives S c (S p q c), a head normal form whose only redex is the argument S p q c. The evolution continues inside
that argument with active list [p, q, c] and c frozen outside: a *descent*. A descent needs a list of exactly three
elements whose first element is S, because any other step leaves at least three elements and so keeps the head redex.
code/unique_redex.py stopped a run at such a step, so the enumerations above and Theorems UR-R/UR-C cover head-unique
runs only. Descents can recur for ever. code/descent_runs.py simulates the term-level evolution with exactly one redex
at every step, descents included (2,000 steps):
* nothing survives up to 8 leaves;
* 9 leaves, three terms: S(SS)S(S(SSS)S) and S(S(SS))(S(SSS))S descend once and then run head-unique, and
  S(S(SS))(S(SS))(SS) descends 1,936 times;
* forever-descending terms (≥ 1,000 descents in 2,000 steps) at 9–14 leaves: 1, 2, 5, 13, 32, 87.

An independent check on plain trees (no hash-consing, no list machine; count every redex, contract the unique one) gives
exactly one redex at each of 400 steps for S(S(SS))(S(SS))(SS), with the depth of the contracted redex growing linearly
(371 after 400 steps). The same holds for SS(SS(S(S(SS))(S(SS))))(SS) over 300 steps. Two earlier statements are
therefore **REFUTED as stated**:
* "every S-term whose evolution has exactly one redex at every step for ever is a linear counter of type A or II"
  (true for head-unique runs; the descending ones are not eventually head runs);
* R57's "no term with ≤ 9 leaves has exactly one redex at every step" (true for the head-unique property; with
  descents the minimum is 9 leaves).
*Novelty (checked 2026-10-26, evening): NOT new.* K·K = S(SS)(SS)(S(SS)(SS)) is the Zachos term STT(STT) (T = SS) of
BEKW §2 (Zachos 1978), whose Böhm tree with subtrees S Z_n in the order 1, 2, 2, 3, 3, 3, … BEKW describe (Fig. 10),
and which this project already recorded in E20. The mechanism is that of our own Theorem C (copy-and-count-down rounds,
different base), whose novelty was withdrawn for the same reason. BEKW also cite a characterization of *all* terms whose
reduction graph is an infinite line, i.e. all one-redex-forever terms: J. Waldmann, "Nimm Zwei", TR IR-432, VU
Amsterdam 1997 (not read; not in literature/). Theorems UR-R, UR-C and DK below very likely overlap with or duplicate
it, so no novelty is claimed for them. What is new is limited to: the Lean formalisation of UR-R/UR-C, the correction of
our own overclaims, and the computer check that all 140 forever-descending one-redex terms up to 14 leaves enter one cycle.
*Theorem DK (the descending K-counter; known mechanism, see above) — PROVED.* Let K = S(SS)(SS), Y_0 = K,
Y_{n+1} = S S Y_n (all normal forms).
For normal Y, Z, p, q:
* (D1) [S, S S Y, Z] → [S, Y, Z] in one step: descent, Z frozen.
* (D2) [S, K, Z] → [SS, SS, Z] in one step: descent, Z frozen.
* (D3) [SS, SS, Z] → [S, Z, S S Z], then, if Z = S p q, a descent to [p, q, S S Z] with S S Z frozen.

Hence from the active list [SS, SS, Y_n] the evolution reaches [SS, SS, Y_{n+1}] in n + 2 steps, with exactly one
redex at every step. Each period has opcode word 1 0^{n+1} and n + 1 descents.
*Proof.* Each rule is one or two head steps. Every list element and every frozen sibling is a normal form, so the head
redex (or the descended argument) is the only redex. From [SS, SS, Y_n]: D3 gives [S, Y_{n−1}, Y_{n+1}] (for n = 0,
[SS, SS, Y_1] at once); D1 applied n − 1 times gives [S, Y_0, Y_{n+1}] = [S, K, Y_{n+1}]; D2 gives [SS, SS, Y_{n+1}]. ∎
code/descent_k_proof.py checks D1–D3 on terms with opaque atoms (exactly one redex in every intermediate term). It
then follows each forever-descending term up to 14 leaves concretely, checking exactly one redex at every step, until
it enters the cycle: **140/140 (53 up to 13 leaves, 87 at 14) enter by step 5, so Theorem DK gives their whole
evolution, PROVED per term.** code/descent_classify.py independently finds the K-cycle steady state in all of them
(steps 500–2,000).
So every forever-descending one-redex evolution found is a descending linear counter: opcode word u ∏ 1 0^{n+1}
(morphic), frozen output S Y_1 (S Y_2 (S Y_2 (S Y_3 (S Y_3 (S Y_3 ⋯))))). Terms with finitely many descents end
head-unique, so Theorems UR-R/UR-C cover their tails.
*Structure of a segment (between descents).* The active list has exactly three elements at a descent and returns to
three only at *low points* [a, b, c]. In a run that keeps exactly one redex the transitions are:
* a = S and b = S p q: descent to [p, q, c];
* a = S and |args b| ≤ 1: the term is a normal form and the evolution ends;
* a = S x and |args b| ≤ 1: [x, c, b c];
* a = S x t and |args b| ≤ 1: an *excursion*. The sub-term S x t c must normalise head-uniquely to some S e f; the next
  low point is then [e, f, b c]. If it never normalises there are no more low points, so no more descents.
* |args b| = 2 with a ≠ S gives a second redex.

No descent can happen inside an excursion, because the full list has at least four elements there. A finite term
cannot make descents peel its second element for ever, so every forever-descending evolution has infinitely many
building segments (T1 or excursion steps).
*Conjecture DK\* — CONJECTURAL (EXPERIMENTALLY SUPPORTED).* Every forever-descending one-redex evolution enters the
K-cycle. The evidence: after a descent the evolution restarts from a 3-element list [p, q, c] of normal forms, so steady
states can be probed by enumerating triples directly (code/descent_triples.py, 2,000 steps).
* All 704,969 triples with p, q, c ≤ 7 leaves: 8 forever-descending.
* All 186,864 triples with p ≤ 10, q ≤ 5, c ≤ 4 leaves: 1 forever-descending.
* Every one of them has the K-cycle steady state.

With Theorem DK this would complete the one-redex class: every S-term with exactly one redex at every step for ever
would be a linear counter, ascending (UR-C) or descending (DK).
