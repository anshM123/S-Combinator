/-
  Proposition MW (a), (b) — the multiway graph of an S-term — machine-checked (main agent, 2026-10-27).
  Plain Lean 4 core, no Mathlib. Reduction contracts ONE redex S x y z ANYWHERE in the term (every evolution order,
  every choice of redex; a parallel step is a finite sequence of such steps).
  * `red_size`: a step never lowers the number of leaves.
  * `red_potential` (MW(a)): a step raises the number of leaves, or keeps it and lowers the sum of leaf depths.
  * `acyclic` (MW(b)): no S-term reduces to itself in one or more steps; the multiway graph of every term is a DAG.
  * `unbounded` (MW(b)): along every infinite evolution the sizes are unbounded, so it visits infinitely many terms.
-/

inductive T where
  | S : T
  | app : T → T → T
deriving DecidableEq, Repr

open T

def size : T → Nat
  | S => 1
  | app f a => size f + size a

/-- sum of the depths of the leaves, the root being at depth d -/
def dsum : T → Nat → Nat
  | S, d => d
  | app f a, d => dsum f (d + 1) + dsum a (d + 1)

/-- one reduction step: contract a redex S x y z anywhere -/
inductive Red : T → T → Prop
  | redex (x y z : T) : Red (app (app (app S x) y) z) (app (app x z) (app y z))
  | left {f f' : T} (a : T) : Red f f' → Red (app f a) (app f' a)
  | right (f : T) {a a' : T} : Red a a' → Red (app f a) (app f a')

/-- one or more steps -/
inductive RedPlus : T → T → Prop
  | single {t u : T} : Red t u → RedPlus t u
  | tail {t u v : T} : RedPlus t u → Red u v → RedPlus t v

theorem size_pos : ∀ t : T, 1 ≤ size t
  | S => by simp [size]
  | app f a => by have := size_pos f; simp only [size]; omega

theorem dsum_succ : ∀ (t : T) (d : Nat), dsum t (d + 1) = dsum t d + size t
  | S, d => by simp [dsum, size]
  | app f a, d => by
    simp only [dsum, size]
    rw [dsum_succ f (d + 1), dsum_succ a (d + 1)]
    omega

/-- the redex S x y S: same size, the leaf-depth sum drops by |x| -/
theorem redex_S (x y : T) (d : Nat) :
    dsum (app (app x S) (app y S)) d + size x = dsum (app (app (app S x) y) S) d := by
  simp only [dsum]
  rw [dsum_succ x (d + 1 + 1)]
  omega

theorem red_size {t u : T} (h : Red t u) : size t ≤ size u := by
  induction h with
  | redex x y z => have := size_pos z; simp only [size]; omega
  | left a _ ih => simp only [size]; omega
  | right f _ ih => simp only [size]; omega

/-- **Proposition MW(a)** (potential): every step raises the size, or keeps it and lowers the leaf-depth sum -/
theorem red_potential {t u : T} (h : Red t u) :
    size t < size u ∨ (size t = size u ∧ ∀ d, dsum u d < dsum t d) := by
  induction h with
  | redex x y z =>
    cases z with
    | S =>
      right
      refine ⟨by simp only [size]; omega, fun d => ?_⟩
      have h1 := redex_S x y d
      have h2 := size_pos x
      omega
    | app z1 z2 =>
      left
      have := size_pos z1
      have := size_pos z2
      simp only [size]; omega
  | left a _ ih =>
    rcases ih with ih | ⟨h1, h2⟩
    · left; simp only [size]; omega
    · right
      refine ⟨by simp only [size]; omega, fun d => ?_⟩
      simp only [dsum]
      have := h2 (d + 1)
      omega
  | right f _ ih =>
    rcases ih with ih | ⟨h1, h2⟩
    · left; simp only [size]; omega
    · right
      refine ⟨by simp only [size]; omega, fun d => ?_⟩
      simp only [dsum]
      have := h2 (d + 1)
      omega

theorem redplus_potential {t u : T} (h : RedPlus t u) :
    size t < size u ∨ (size t = size u ∧ ∀ d, dsum u d < dsum t d) := by
  induction h with
  | single h => exact red_potential h
  | tail _ h2 ih =>
    have h3 := red_potential h2
    rcases ih with ih | ⟨e1, e2⟩
    · left
      rcases h3 with h3 | ⟨e3, _⟩
      · omega
      · omega
    · rcases h3 with h3 | ⟨e3, e4⟩
      · left; omega
      · right; exact ⟨by omega, fun d => Nat.lt_trans (e4 d) (e2 d)⟩

/-- **Proposition MW(b)** (acyclicity): no S-term reduces to itself in one or more steps -/
theorem acyclic (t : T) : ¬ RedPlus t t := by
  intro h
  rcases redplus_potential h with h | ⟨_, h⟩
  · omega
  · have := h 0
    omega

abbrev LexR2 := Prod.Lex (fun a₁ a₂ : Nat => a₁ < a₂) (fun a₁ a₂ : Nat => a₁ < a₂)

theorem lexA {a a' b b' : Nat} (h : a < a') : LexR2 (a, b) (a', b') := Prod.Lex.left _ _ h
theorem lexB {a a' b b' : Nat} (h1 : a = a') (h : b < b') : LexR2 (a, b) (a', b') := by
  subst h1; exact Prod.Lex.right _ h

theorem no_bounded_evolution (s : Nat → T) (hs : ∀ n, Red (s n) (s (n + 1))) (N : Nat)
    (hb : ∀ n, size (s n) ≤ N) (n : Nat) : False := by
  have h := red_potential (hs n)
  have hb0 := hb n
  have hb1 := hb (n + 1)
  exact no_bounded_evolution s hs N hb (n + 1)
termination_by (N - size (s n), dsum (s n) 0)
decreasing_by
  rcases h with h | ⟨e, h⟩
  · exact lexA (by omega)
  · exact lexB (by omega) (h 0)

/-- **Proposition MW(b)** (sizes diverge): along every infinite evolution (any order, any choice of redexes) the size
    exceeds every bound; in particular an infinite evolution visits infinitely many distinct terms -/
theorem unbounded (s : Nat → T) (hs : ∀ n, Red (s n) (s (n + 1))) (N : Nat) : ∃ n, N < size (s n) := by
  cases Classical.em (∃ n, N < size (s n)) with
  | inl h => exact h
  | inr h =>
    exfalso
    apply no_bounded_evolution s hs N _ 0
    intro n
    cases Nat.lt_or_ge N (size (s n)) with
    | inl h' => exact absurd ⟨n, h'⟩ h
    | inr h' => exact h'

#print axioms red_potential
#print axioms acyclic
#print axioms unbounded
