
namespace SC

open C
open C.T
open FM
open DP

/-- **EM from one strict cut on a non-tower stack.**  A jump-free infinite leftmost walk that has ONE strict cut (a time
    t after which the depth stays strictly above the depth of u t) whose stack is a non-tower is eventually monotone.
    (No hypothesis on the depth otherwise.) -/
theorem EM_of_cut (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t : Nat) (hσ : ¬ Tower (SA.rpart (u t)))
    (hcut : ∀ e, SA2.msl (u t) < SA2.msl (u (t + 1 + e))) :
    ∃ j0, ∀ j, j0 ≤ j → 3 ≤ (args (u j)).length ∧ u (j + 1) ≠ SA.rpart (u j) := by
  have hc := hchild t
  match hut : u t with
  | S => rw [hut] at hc; exact absurd hc (CA.no_child_S _)
  | app q σ =>
    rw [hut] at hc hσ hcut
    simp only [SA.rpart] at hσ
    rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, dd, hrr⟩
    · exfalso
      rw [args_app] at hlen hrr
      match hq : args q, hlen, hrr with
      | [], _, hrr =>
        simp only [List.nil_append, List.cons.injEq] at hrr
        have := hcut 0
        rw [Nat.add_zero, ← hrr.1] at this
        simp only [SA2.msl] at this
        omega
      | [p], _, _ => exact hnj t p σ (by rw [hut, TC.args_one' q p hq])
      | _ :: _ :: _, hlen, _ => simp at hlen
    · rw [args_app] at hlen
      have hq2 : 2 ≤ (args q).length := by simp at hlen; omega
      obtain ⟨K, c, hK, hch⟩ := fib_step q σ _ dd hq2 hσ hrr
      have hm := (msl_Fw σ c K).1
      rw [← hch] at hm
      have hup := hcut 0
      rw [Nat.add_zero, hm] at hup
      simp only [SA2.msl] at hup
      match K, hK, hch with
      | 0, _, _ => omega
      | 1, _, _ => omega
      | 2, hK, _ =>
        exact ⟨t, fun j hj => by
          have := cut_monotone u hchild hnj t q σ c hut hσ hq2 hK (by rw [hut]; exact hcut) (j - t)
          rwa [show t + (j - t) = j by omega] at this⟩
      | 3, hK, _ =>
        obtain ⟨t2, ht2⟩ := K3_monotone u hchild hnj t q σ c hut hσ hq2 hK
        exact ⟨t2, fun j hj => by
          have := ht2 (j - t2)
          rwa [show t2 + (j - t2) = j by omega] at this⟩
      | K + 4, _, hch =>
        exfalso
        have hntw : ∀ i, ¬ Tower (Fw σ c i) := fun i => SA3.fw_nontower _ c hσ i
        have e : Fw σ c (K + 4) = app (app (Fw σ c K) (Fw σ c (K + 1))) (Fw σ c (K + 3)) := by
          rw [show K + 4 = (K + 2) + 2 by omega, Fw_add2, Fw_add2]
        rw [e] at hch
        obtain ⟨k1, _, hk1, _⟩ := gamma_walk u hchild hnj (t + 1) _ _ _ hch (hntw (K + 1)) (hntw (K + 3))
        exact hntw K ⟨k1 + 1, hk1⟩

/-- **The leftmost finite half for flag 0 from (J) and (NT').**  (NT'): if the depth tends to infinity, some strict cut
    of the (eventually jump-free) walk sits on a non-tower stack. -/
theorem finite_half_of_J_NT2 (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hflag : FH.flag (u 0) = false)
    (hJ : ∃ N, ∀ j, N ≤ j → ∀ p τ, u j ≠ app (app S p) τ)
    (hNT : ∀ N, (∀ j, N ≤ j → ∀ p τ, u j ≠ app (app S p) τ) → (∀ d, ∃ M, ∀ j, M ≤ j → d < SA2.msl (u j)) →
      ∃ t, N ≤ t ∧ ¬ Tower (SA.rpart (u t)) ∧ ∀ e, SA2.msl (u t) < SA2.msl (u (t + 1 + e))) : False := by
  apply CA.finite_half_of_J_EMdeep u hchild hflag hJ
  intro hdeep
  obtain ⟨N, hN⟩ := hJ
  obtain ⟨t, hNt, hσ, hcut⟩ := hNT N hN hdeep
  let v : Nat → T := fun j => u (t + j)
  have hv : ∀ j, FH.LChild (v j) (v (j + 1)) := fun j => by
    show FH.LChild (u (t + j)) (u (t + (j + 1)))
    rw [show t + (j + 1) = t + j + 1 by omega]; exact hchild (t + j)
  have hvnj : ∀ j p τ, v j ≠ app (app S p) τ := fun j p τ => hN (t + j) (by omega) p τ
  obtain ⟨j0, hj0⟩ := EM_of_cut v hv hvnj 0 (by show ¬ Tower (SA.rpart (u (t + 0))); exact hσ)
    (fun e => by
      show SA2.msl (u (t + 0)) < SA2.msl (u (t + (0 + 1 + e)))
      rw [Nat.add_zero, show t + (0 + 1 + e) = t + 1 + e by omega]; exact hcut e)
  refine ⟨t + j0, fun j hj => ?_⟩
  have h := hj0 (j - t) (by omega)
  have h1 : 3 ≤ (args (u (t + (j - t)))).length ∧ u (t + (j - t + 1)) ≠ SA.rpart (u (t + (j - t))) := h
  rw [show t + (j - t) = j by omega, show t + (j - t + 1) = j + 1 by omega] at h1
  exact h1

end SC

#print axioms SC.EM_of_cut
#print axioms SC.finite_half_of_J_NT2
