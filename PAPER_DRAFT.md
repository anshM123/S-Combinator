# Böhm-tree dynamics of the S combinator: finite models, a parity theorem, and obstructions to universality

*Draft — not for release without approval. Status labels follow PROOF.md: PROVED / COMPUTATIONALLY CERTIFIED /
EXPERIMENTALLY SUPPORTED / CONJECTURAL.*

## Abstract
We study the computational power of the S combinator (S x y z → x z (y z)) through its Böhm trees. (1) We prove that
Böhm-tree finiteness of S-terms can count modulo 2: the Böhm tree of S^{k+3}(SSS)(SS) is finite iff k is even.
(2) We learn small finite S-models (magmas satisfying the S-identity) that decide productivity (39 elements), Böhm-tree
finiteness (131), infinity of the leftmost (36) and rightmost (19) Böhm-tree paths; each agrees with brute force on every
term up to 19 (resp. 14) leaves, and in every case the only non-trivial counting is modulo 2. For productivity and
finiteness, one half of correctness follows from Question 10 of Barendregt–Endrullis–Klop–Waldmann, and the other half is
certified term by term up to 19 leaves. (3) We prove structural obstructions for emulating counter machines along Böhm-tree
paths: data conservation, global writes, and a potential argument showing that no bounded-cost simulation of a
two-counter machine exists (Theorem O). (4) Any emulation of a machine along a Böhm-tree path whose halting configurations
can be made to diverge reduces halting to infinity of that path (Proposition R); hence, if the learned path models are
correct, no such universal emulation exists. These results do not settle Wolfram's question but localise the remaining
gap precisely.

## 1. Setting
* **Head machine.** Head reduction of S e1 … em is the list machine [a, b, c] ++ R ⇒ ch(a) ++ [c, b·c] ++ R, where ch(a)
  is the list of spine arguments of a; a head normal form (hnf) is a list of length ≤ 2 (terms S, S p, S p q).
* **Böhm tree** BT(t): ⊥ if t has no hnf; otherwise S applied to the Böhm trees of the components of its hnf.
* **Finite S-model:** a finite magma (M, ·) with s ∈ M such that s·x·y·z = x·z·(y·z); the class [t] of a term is its value.
  Classes are invariant under conversion (Lemma 3).
* **M35** (≅ BEKW Fig. 14): if [t]_M35 = ⊥ then t has no hnf (Theorem A). The converse is BEKW **Question 10** (open as far
  as we know; verified for all terms ≤ 19 leaves).

## 2. Böhm-tree finiteness counts modulo 2 (Theorem P2) — PROVED
Let X = SSS, Y = SS, T_j = S applied to the j+2 spine arguments S,…,S (j copies), X, Y.
**Theorem.** BT(T_j) is finite iff j is even or j = 1.
*Proof sketch* (full proof: PROOF.md, Theorem P2). (a) Run lemma: [S^{×m}, c] ++ R ⇒^{m−1} [c, B_{m−1} c] ++ R.
(b) Hence T_j →^{j+3} S (S Y T_{j−2}) (T_{j−2} (S Y T_{j−2})) for j ≥ 2. (c) M35 assigns ⊥ to T_j (S Y T_j) for every j ≠ 1
(the class of the prefix reaches a fixed point at j = 4), so these terms have no hnf. (d) T_1 (S Y T_1) has an infinite
Böhm-tree path through the self-incrementing counter V_{r+1} = S Y V_r. (e) Induction on j. ∎
*Consequence.* Böhm-tree finiteness is not counter-free (contrary to our earlier conjecture), yet it is still recognised
by a finite model (Section 3) — S-terms can count modulo 2 and, as far as all evidence goes, not modulo anything else.

## 3. Finite S-models for Böhm-tree properties — EXPERIMENTALLY SUPPORTED (finite facts CERTIFIED)
Learned with an Angluin-style algorithm (classes = signatures over learned contexts; counterexamples from exhaustive small
terms, random terms, the table's own observations, and violations of the S-identity).

| property | size | S-identity | monoid | exhaustive agreement |
|---|---|---|---|---|
| has hnf (M35) | 35 | exact | aperiodic | ≤ 19 leaves |
| productive (no ⊥) | 39 | exact | aperiodic (951) | ≤ 19 leaves + certificates |
| Böhm tree finite | 131 | exact | period 2 (17,031) | ≤ 19 leaves + certificates |
| leftmost path infinite | 36 | exact | period 2 (809) | 10–16 leaves |
| rightmost path infinite | 19 | exact | aperiodic (184) | 12–16 leaves (audit) |
| LO-evaluation path infinite | 204 | exact | period 2 (45,486) | ≤ 18 leaves |
| branching infinity (two infinite subtrees at a node) | 423 | exact | parity only (sampled) | ≤ 16 leaves |

**Proposition Q (PROVED, conditional on Question 10).** If Question 10 holds, every term with productive class is
productive. *Proof:* the generated sub-magma of P39 × M35 (113 elements, certified) has no (productive, ⊥) pair; with
Q10 such a term has an hnf, whose components again have productive classes (s x y productive ⟺ x, y productive in the
table); coinduction. **Proposition Q′** (same argument): with Question 10, every term with an "infinite" class of the
131-element model has an infinite Böhm tree.
**Certificates (CERTIFIED for all terms ≤ 19 leaves).** Every non-productive-class term has an explicit Böhm-tree path to
a node without hnf (≈547M certificates); every finite-class term has an explicitly explored finite Böhm tree (≈652M).

## 4. Obstructions to register machines along Böhm-tree paths — PROVED (independently audited)
* **Data conservation (Lemma 8).** With opaque variables, a head step never decreases the number of variable-containing
  list elements unless it opens a variable-headed one. Hence S-terms cannot take three opaque arguments without inspecting
  one (or diverging).
* **Global writes (Theorem J).** In a terminating non-inspecting run, a closed term can be applied to data at most once,
  and only to an element containing all data.
* **Full-read principle (Lemma 11).** A terminating head run of a closed S e1…em fully reads all but at most two arguments.
* **Theorem N\*.** Along Böhm-tree paths that never read two disjoint occurrences x, y, a per-occurrence potential of x
  (closed layers above it) never increases.
* **Theorem O.** For two unary counters ⟨n⟩_i = L_i^n[Z_i] at exact checkpoints C_q[⟨a⟩,⟨b⟩], a counter can gain more than a
  constant only in stretches of cost ≥ a/2 − O(1) (cost = head steps + Böhm-tree steps). Consequently no bounded-cost
  simulation of an INC-loop, a transfer loop, or a Minsky universal two-counter machine exists; transfers cost Ω(a²).

## 5. Halting in Böhm-tree shape for modular emulations (Proposition R) — PROVED (independently audited)
If a machine is emulated along a path rule ρ (leftmost, rightmost, or leftmost-outermost) with at least one Böhm-tree step
per machine step, and halting configurations can be replaced by Ω·N (Ω without hnf), then the machine halts iff the
ρ-path is finite and ends in ⊥ (modularity — a computable modified encoder placing Ω N at halting — is an assumption,
not derived from universality). **Corollary.** If "the ρ-path is infinite" is decidable, no universal machine has such a
modular emulation, whatever decoder is used. With the learned path models (Section 3), this excludes modular universal
emulations along leftmost and rightmost paths, conditional on those models' correctness.

## 6. What remains
1. **Question 10** and the termination halves of the learned models (all are termination statements; a type-theoretic
   reformulation shows Q10 ⟺ soundness of a recursive intersection-type assignment, PROOF.md).
2. **Modularity at halting:** excluded emulations whose halting cannot be made to diverge (syntactic decoders only).
3. **Conjecture C9:** every MSO property of Böhm trees of S-terms has a finite S-model (⇒ no universal emulation with a
   Böhm-tree-shape halting signal); **C10:** only parity counting occurs.

## References
Barendregt, Endrullis, Klop, Waldmann, *Dance of the Starlings* (2017). Barendregt, Manzonetto, *A Lambda Calculus
Satellite* (2022), Ch. 7 (Padovani). Manzonetto, FSCD 2023 invited paper. Waldmann (RTA 1998; Inf. & Comp. 2000).
Cheilaris, Ramirez, Zachos. Wolfram, *Combinators: A Centennial View* (2021) and the S Combinator Challenge.
