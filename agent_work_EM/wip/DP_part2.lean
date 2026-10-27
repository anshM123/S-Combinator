
namespace DP

open C
open C.T
open FM

/-- **Jump classification over a non-tower bottom.**  If the leftmost child of the node Q.v (Q with >= 2 arguments,
    v a non-tower) is a jump node S p τ, then H(Q) = S (tw K) c0 with
    K = 0: v = S p τ (the walk returned onto a stack level whose multiplier is S p);
    K = 1: c0 = S p and τ = v (a DISCARD jump: the rightmost child of Q is S p, the stack v is dropped);
    K = 2: v = S p and τ = c0.v (the jump target p lies below an S on the stack);
    K = 3: c0 = S and p = v (the jump target is the stack v itself). -/
theorem jump_child (Q v p τ d : T) (hQ : 2 ≤ (args Q).length) (hv : ¬ Tower v)
    (h : Reach (args (app Q v)) [app (app S p) τ, d]) :
    ∃ c0, (Reach (args Q) [tw 0, c0] ∧ v = app (app S p) τ) ∨
      (Reach (args Q) [tw 1, c0] ∧ c0 = app S p ∧ τ = v) ∨
      (Reach (args Q) [tw 2, c0] ∧ v = app S p ∧ τ = app c0 v) ∨
      (Reach (args Q) [tw 3, c0] ∧ c0 = S ∧ p = v) := by
  obtain ⟨K, c0, hK, hch⟩ := fib_step Q v _ d hQ hv h
  refine ⟨c0, ?_⟩
  match K, hK, hch with
  | 0, hK, hch => exact Or.inl ⟨hK, hch.symm⟩
  | 1, hK, hch =>
    have e : Fw v c0 1 = app c0 v := rfl
    rw [e] at hch
    simp only [app.injEq] at hch
    exact Or.inr (Or.inl ⟨hK, hch.1.symm, hch.2⟩)
  | 2, hK, hch =>
    rw [show (2 : Nat) = 0 + 2 from rfl, Fw_add2] at hch
    simp only [app.injEq] at hch
    have e : Fw v c0 (0 + 1) = app c0 v := rfl
    exact Or.inr (Or.inr (Or.inl ⟨hK, hch.1.symm, by rw [← e]; exact hch.2⟩))
  | 3, hK, hch =>
    rw [show (3 : Nat) = 1 + 2 from rfl, Fw_add2] at hch
    simp only [app.injEq] at hch
    have e : Fw v c0 1 = app c0 v := rfl
    rw [e] at hch
    simp only [app.injEq] at hch
    exact Or.inr (Or.inr (Or.inr ⟨hK, hch.1.1.symm, hch.1.2⟩))
  | i + 4, _, hch =>
    exfalso
    rw [show i + 4 = (i + 2) + 2 by omega, Fw_add2, Fw_add2] at hch
    simp only [app.injEq] at hch
    -- Fw v c0 i = S, impossible for a non-tower v
    exact SA3.fw_nontower v c0 hv i (hch.1.1 ▸ tower_S)

end DP

#print axioms DP.jump_child
