
namespace DP

open C
open C.T
open FM

/-- **Tower letters are frozen.**  In a jump-free leftmost walk, once a stack segment tw (k+1).ρ (a tower letter on
    top of ρ) is a right-spine suffix of a node, it stays a PROPER right-spine suffix of every later node: the node
    tw (k+1).ρ = S (tw k) ρ is a jump node and is never visited, and non-jump steps keep proper suffixes. -/
theorem tower_letter_frozen (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t k : Nat) (ρ : T) (hs : Suf (app (tw (k + 1)) ρ) (u t)) :
    ∀ e, Suf (app (tw (k + 1)) ρ) (u (t + e)) ∧ u (t + e) ≠ app (tw (k + 1)) ρ := by
  have hne : ∀ s, u s ≠ app (tw (k + 1)) ρ := fun s h => hnj s (tw k) ρ (by rw [h]; rfl)
  intro e
  induction e with
  | zero => exact ⟨hs, hne t⟩
  | succ e ih =>
    refine ⟨?_, hne _⟩
    rw [show t + (e + 1) = t + e + 1 by omega]
    exact SA.step_keeps _ _ _ (hchild (t + e)) ih.1 ih.2 (hnj (t + e))

/-- ... and the walk stays strictly above it: the right-spine depth never drops to the level of the tower letter. -/
theorem tower_letter_depth (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t k : Nat) (ρ : T) (hs : Suf (app (tw (k + 1)) ρ) (u t)) :
    ∀ e, SA2.msl (app (tw (k + 1)) ρ) < SA2.msl (u (t + e)) := by
  intro e
  obtain ⟨h1, h2⟩ := tower_letter_frozen u hchild hnj t k ρ hs e
  generalize u (t + e) = x at h1 h2
  cases x with
  | S => exact absurd (suf_S _ h1).symm (by intro h; cases h)
  | app p y =>
    rcases suf_app_inv _ p y h1 with h | h
    · exact absurd h h2
    · have := SA2.msl_suf _ _ h
      simp only [SA2.msl] at this ⊢
      omega

end DP

#print axioms DP.tower_letter_frozen
#print axioms DP.tower_letter_depth
