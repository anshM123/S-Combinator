
namespace CA

open C
open C.T
open FM

/-- **The remaining gap, precisely.**  Let u be an infinite leftmost walk from an L36-flag-0 term.  If u has only
    finitely many jumps (nodes S p τ) and — in case its right-spine depth tends to infinity — is eventually monotone,
    we get a contradiction.  So the leftmost finite half for flag 0 follows from (J) every infinite leftmost walk has
    finitely many jumps, and (EM_deep) every eventually jump-free infinite leftmost walk whose depth tends to infinity
    is eventually monotone.  (Scenario A — depth not tending to infinity — needs no conjecture any more.) -/
theorem finite_half_of_J_EMdeep (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hflag : FH.flag (u 0) = false)
    (hJ : ∃ N, ∀ j, N ≤ j → ∀ p τ, u j ≠ app (app S p) τ)
    (hEMd : (∀ d, ∃ N, ∀ j, N ≤ j → d < SA2.msl (u j)) →
      ∃ j0, ∀ j, j0 ≤ j → 3 ≤ (args (u j)).length ∧ u (j + 1) ≠ SA.rpart (u j)) : False := by
  obtain ⟨N, hN⟩ := hJ
  let v : Nat → T := fun j => u (N + j)
  have hv : ∀ j, FH.LChild (v j) (v (j + 1)) := fun j => by
    show FH.LChild (u (N + j)) (u (N + (j + 1)))
    rw [show N + (j + 1) = N + j + 1 by omega]; exact hchild (N + j)
  have hvflag : FH.flag (v 0) = false := by
    show FH.flag (u (N + 0)) = false
    rw [FH.flag_walk u hchild (N + 0)]; exact hflag
  have hvnj : ∀ j p τ, v j ≠ app (app S p) τ := fun j p τ => hN (N + j) (by omega) p τ
  have hdeep := depth_to_infinity v hv hvflag hvnj
  apply EM.finite_half_of_EM u hchild hflag
  apply hEMd
  intro d
  obtain ⟨M, hM⟩ := hdeep d
  refine ⟨N + M, fun j hj => ?_⟩
  have h1 : d < SA2.msl (u (N + (j - N))) := hM (j - N) (by omega)
  rwa [show N + (j - N) = j by omega] at h1

end CA

#print axioms CA.finite_half_of_J_EMdeep
