
namespace SC

open C
open C.T
open FM
open DP

theorem Twr2_shift (Y : T) : ∀ k, Twr2 Y (k + 1) = Twr2 (app (tw 2) Y) k
  | 0 => rfl
  | k + 1 => by
    show app (tw 2) (Twr2 Y (k + 1)) = app (tw 2) (Twr2 (app (tw 2) Y) k)
    rw [Twr2_shift Y k]

theorem size_app_ne (a b : T) : app a b ≠ b := OM.size_app_ne a b

theorem msl_app (a b : T) : SA2.msl (app a b) = SA2.msl b + 1 := rfl

/-- the invariant of the generalized Omega cycle with base program b (b 0 = Y) and push letter S(SS) -/
def CycInv (Y : T) (i0 : Nat) (b : Nat → T) (x : T) : Prop :=
  ∃ m, (∃ k, 1 ≤ k ∧ k ≤ m ∧ x = app (Twr2 Y k) (Twr2 Y (m + 1))) ∨
    (∃ i, i ≤ i0 ∧ x = app (b i) (Twr2 Y (m + 1)))

/-- one step of the cycle: the invariant is kept and the step is monotone (>= 3 args, child /= last argument) -/
theorem cyc_step (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (Y : T) (hY : ¬ Tower Y) (i0 : Nat) (b : Nat → T)
    (hBC : BaseChain Y i0 b 2 (tw 2)) (s : Nat) (hI : CycInv Y i0 b (u s)) :
    CycInv Y i0 b (u (s + 1)) ∧ 3 ≤ (args (u s)).length ∧ u (s + 1) ≠ SA.rpart (u s) := by
  obtain ⟨hb0, htail, hlast2, hlast, _⟩ := hBC
  have hnt : ∀ k, ¬ Tower (Twr2 Y k) := Twr2_nontower Y hY
  obtain ⟨m, ⟨k, hk1, hkm, hx⟩ | ⟨i, hi, hx⟩⟩ := hI
  · -- a skip node
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hx' : u s = app (app (tw 2) (Twr2 Y k')) (Twr2 Y (m + 1)) := hx
    obtain ⟨kk, _, hkk, h1⟩ := gamma_walk u hchild hnj s (tw 2) _ _ hx' (hnt k') (hnt (m + 1))
    have := SA3.tw_inj 2 (kk + 1) hkk
    obtain rfl : kk = 1 := by omega
    have e : Fw (Twr2 Y (m + 1)) (Twr2 Y k') 1 = app (Twr2 Y k') (Twr2 Y (m + 1)) := rfl
    rw [e] at h1
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      cases k' with
      | zero => exact ⟨m, Or.inr ⟨0, Nat.zero_le _, by rw [hb0]; rfl⟩⟩
      | succ k'' => exact ⟨m, Or.inl ⟨k'' + 1, by omega, by omega, rfl⟩⟩
    · rw [hx]; show 3 ≤ (args (Twr2 Y (k' + 1)) ++ [Twr2 Y (m + 1)]).length
      show 3 ≤ (args (app (tw 2) (Twr2 Y k')) ++ [Twr2 Y (m + 1)]).length
      simp [args, tw]
    · rw [h1, hx]; exact size_app_ne _ _
  · -- a base node
    have h2 : 2 ≤ (args (b i)).length := by
      by_cases h : i < i0
      · exact (htail i h).1
      · obtain rfl : i = i0 := by omega
        exact hlast2
    have h3 : 3 ≤ (args (u s)).length := by rw [hx, args_app]; simp; omega
    by_cases hlt : i < i0
    · obtain ⟨h2', hr⟩ := htail i hlt
      have h1 := fib_next u hchild s (b i) _ (b (i + 1)) 1 (hnt (m + 1)) h2' hx hr
      have e : Fw (Twr2 Y (m + 1)) (b (i + 1)) 1 = app (b (i + 1)) (Twr2 Y (m + 1)) := rfl
      rw [e] at h1
      refine ⟨⟨m, Or.inr ⟨i + 1, by omega, h1⟩⟩, h3, ?_⟩
      rw [h1, hx]; exact size_app_ne _ _
    · obtain rfl : i = i0 := by omega
      have h1 := fib_next u hchild s (b i) _ (tw 2) 2 (hnt (m + 1)) hlast2 hx hlast
      have e : Fw (Twr2 Y (m + 1)) (tw 2) 2 = app (Twr2 Y (m + 1)) (Twr2 Y (m + 2)) := rfl
      rw [e] at h1
      refine ⟨⟨m + 1, Or.inl ⟨m + 1, by omega, by omega, h1⟩⟩, h3, ?_⟩
      rw [h1, hx]; simp only [SA.rpart]
      intro h; have := congrArg size h; simp [size] at this
      have := size_pos (Twr2 Y (m + 2)); have := size_pos (Twr2 Y (m + 1))
      have : size (Twr2 Y (m + 2)) = size (tw 2) + size (Twr2 Y (m + 1)) := rfl
      omega

/-- the cycle runs forever and is monotone -/
theorem cyc_forever (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (Y : T) (hY : ¬ Tower Y) (i0 : Nat) (b : Nat → T)
    (hBC : BaseChain Y i0 b 2 (tw 2)) (s : Nat) (hI : CycInv Y i0 b (u s)) :
    ∀ e, 3 ≤ (args (u (s + e))).length ∧ u (s + e + 1) ≠ SA.rpart (u (s + e)) := by
  have hall : ∀ e, CycInv Y i0 b (u (s + e)) := by
    intro e
    induction e with
    | zero => exact hI
    | succ e ih =>
      rw [show s + (e + 1) = s + e + 1 by omega]
      exact (cyc_step u hchild hnj Y hY i0 b hBC (s + e) ih).1
  intro e
  exact (cyc_step u hchild hnj Y hY i0 b hBC (s + e) (hall e)).2

end SC

#print axioms SC.cyc_step
#print axioms SC.cyc_forever
