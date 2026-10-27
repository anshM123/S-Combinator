
namespace DP

open C
open C.T
open FM

/-- **The finite half from (J) + (TP_deep).**  An infinite leftmost walk from an L36-flag-0 term is impossible if
    (J) it makes only finitely many jumps, and (TP_deep) when its depth tends to infinity, from some time on its stacks
    are non-towers and every computed step pushing K >= 2 multipliers is a push of a tower letter
    (H(q) = S (tw 2) (tw (k+1))).  Uses CA.depth_to_infinity (Scenario A closed), DP.EM_of_TP and
    EM.finite_half_of_EM. -/
theorem finite_half_of_J_TP (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hflag : FH.flag (u 0) = false)
    (hJ : ∃ N, ∀ j, N ≤ j → ∀ p τ, u j ≠ app (app S p) τ)
    (hTP : (∀ d, ∃ N, ∀ j, N ≤ j → d < SA2.msl (u j)) → ∃ T, ∀ t, T ≤ t → ¬ Tower (SA.rpart (u t)) ∧
      ∀ q σ K c, u t = app q σ → 2 ≤ (args q).length → Reach (args q) [tw K, c] → 2 ≤ K →
        K = 2 ∧ ∃ k, c = tw (k + 1)) : False := by
  apply CA.finite_half_of_J_EMdeep u hchild hflag hJ
  intro hdeep
  obtain ⟨N, hN⟩ := hJ
  obtain ⟨T0, hT⟩ := hTP hdeep
  let v : Nat → T := fun j => u (N + j)
  have hv : ∀ j, FH.LChild (v j) (v (j + 1)) := fun j => by
    show FH.LChild (u (N + j)) (u (N + (j + 1)))
    rw [show N + (j + 1) = N + j + 1 by omega]; exact hchild (N + j)
  have hvnj : ∀ j p τ, v j ≠ app (app S p) τ := fun j p τ => hN (N + j) (by omega) p τ
  have hvdeep : ∀ d, ∃ M, ∀ j, M ≤ j → d < SA2.msl (v j) := by
    intro d
    obtain ⟨M, hM⟩ := hdeep d
    exact ⟨M, fun j hj => hM (N + j) (by omega)⟩
  obtain ⟨j0, hj0⟩ := EM_of_TP v hv hvnj hvdeep T0 (fun t ht => hT (N + t) (by omega))
  refine ⟨N + j0, fun j hj => ?_⟩
  have h := hj0 (j - N) (by omega)
  have e1 : N + (j - N) = j := by omega
  have e2 : N + (j - N + 1) = j + 1 := by omega
  have h1 : 3 ≤ (args (u (N + (j - N)))).length ∧ u (N + (j - N + 1)) ≠ SA.rpart (u (N + (j - N))) := h
  rw [e1, e2] at h1
  exact h1

end DP

#print axioms DP.finite_half_of_J_TP
