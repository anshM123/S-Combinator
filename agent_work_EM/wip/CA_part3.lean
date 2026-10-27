
namespace CA

open C
open C.T
open FM

theorem msl_zero (x : T) (h : SA2.msl x = 0) : x = S := by
  cases x with
  | S => rfl
  | app f y => simp [SA2.msl] at h

theorem no_child_S (u' : T) (h : FH.LChild S u') : False := by
  rcases h with ⟨_, rest, hr⟩ | ⟨hlen, _⟩
  · simp [args] at hr
  · simp [args] at hlen

/-- **Scenario A is impossible for flag 0 (depth form).**  In a jump-free infinite leftmost walk from a term whose L36
    class has flag 0, the right-spine depth tends to infinity. -/
theorem depth_to_infinity (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hflag : FH.flag (u 0) = false) (hnj : ∀ j p τ, u j ≠ app (app S p) τ) :
    ∀ d, ∃ N, ∀ j, N ≤ j → d < SA2.msl (u j) := by
  intro d
  induction d with
  | zero =>
    refine ⟨0, fun j _ => ?_⟩
    refine Nat.pos_of_ne_zero (fun h => ?_)
    have := msl_zero _ h
    have hc := hchild j
    rw [this] at hc
    exact no_child_S _ hc
  | succ d ih =>
    obtain ⟨N, hN⟩ := ih
    refine Classical.byContradiction (fun hn => ?_)
    have hinf : ∀ M, ∃ j, M ≤ j ∧ SA2.msl (u (N + j)) = d + 1 := by
      intro M
      refine Classical.byContradiction (fun hno => hn ⟨N + M, fun j hj => ?_⟩)
      have h1 := hN j (by omega)
      refine Classical.byContradiction (fun h2 => hno ⟨j - N, by omega, ?_⟩)
      rw [show N + (j - N) = j by omega]
      omega
    let v : Nat → T := fun j => u (N + j)
    have hv : ∀ j, FH.LChild (v j) (v (j + 1)) := fun j => by
      show FH.LChild (u (N + j)) (u (N + (j + 1)))
      rw [show N + (j + 1) = N + j + 1 by omega]
      exact hchild (N + j)
    have hvnj : ∀ j p τ, v j ≠ app (app S p) τ := fun j p τ => hnj (N + j) p τ
    have hlow : ∀ j, d + 1 ≤ SA2.msl (v j) := fun j => hN (N + j) (by omega)
    have h1 := SA3.scenarioA_depth_one v hv hvnj (d + 1) (by omega) hlow hinf
    have hd0 : d = 0 := by omega
    subst hd0
    have hvflag : FH.flag (v 0) = false := by
      show FH.flag (u (N + 0)) = false
      rw [FH.flag_walk u hchild (N + 0)]; exact hflag
    apply no_caseA v hv hvflag hvnj
    intro M
    obtain ⟨j, hj, hm⟩ := hinf M
    refine ⟨j, hj, ?_⟩
    show ∃ q, u (N + j) = app q S
    match hvj : u (N + j) with
    | S => rw [hvj] at hm; simp [SA2.msl] at hm
    | app q z =>
      refine ⟨q, ?_⟩
      rw [hvj] at hm
      simp only [SA2.msl] at hm
      rw [msl_zero z (by omega)]

end CA

#print axioms CA.depth_to_infinity
