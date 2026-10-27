
namespace SC

open C
open C.T
open FM
open DP

/-- **A read of a copy over a stack it cannot leave dies.**  If u s = σ.(σ.Z) (σ, Z non-towers) and the walk never
    visits σ.Z from s on, we get a contradiction: the copy σ is read (S(SS)-skips), and its first other letter, its
    base program's final step, or the copied stack met as a letter, all lead to a jump node, to σ.Z, or to a node that
    contradicts the reading lemma. -/
theorem no_escape (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (s : Nat) (σ Z : T) (hσ : ¬ Tower σ) (hZ : ¬ Tower Z)
    (hs : u s = app σ (app σ Z)) (hno : ∀ e, u (s + e) ≠ app σ Z) : False := by
  have hX : ¬ Tower (app σ Z) := app_nontower _ _ hZ
  obtain ⟨n, Y, hσY, hYn⟩ := twr2_decomp σ
  have hY : ¬ Tower Y := by
    rintro ⟨mY, hmY⟩
    cases n with
    | zero => exact hσ ⟨mY, by rw [hσY, hmY]; rfl⟩
    | succ n1 =>
      have hs1 := tw2_skips u hchild hnj (app (tw 2) Y) (app σ Z) (twr2_tw2_nontower Y) hX n1 s
        (by rw [hs]; conv => lhs; arg 1; rw [hσY, Twr2_shift])
      have hb2 : 2 ≤ (args (app (tw 2) Y)).length := by simp [args, tw]
      have hr : Reach (args (app (tw 2) Y)) [tw 1, Y] := Reach.refl
      have h2 := fib_next u hchild (s + n1) (app (tw 2) Y) (app σ Z) Y 1 hX hb2 hs1 hr
      have e1 : Fw (app σ Z) Y 1 = app Y (app σ Z) := rfl
      rw [e1, hmY] at h2
      cases mY with
      | zero =>
        have hc2 := hchild (s + n1 + 1)
        rw [h2] at hc2
        rcases hc2 with ⟨_, rest, hrr⟩ | ⟨hlen, _, _⟩
        · simp only [tw, args, List.nil_append, List.cons.injEq] at hrr
          exact hno (n1 + 2) (by rw [show s + (n1 + 2) = s + n1 + 1 + 1 by omega]; exact hrr.1.symm)
        · simp [args, tw] at hlen
      | succ m1 => exact hnj _ (tw m1) (app σ Z) h2
  have hs0 : u (s + n) = app Y (app σ Z) :=
    tw2_skips u hchild hnj Y (app σ Z) hY hX n s (by rw [hs]; conv => lhs; arg 1; rw [hσY])
  match Y, hY, hYn, hσY, hs0 with
  | S, hY, _, _, _ => exact hY ⟨0, rfl⟩
  | app l ρ, hY, hYn, hσY, hs0 =>
  by_cases hρ : Tower ρ
  · obtain ⟨i0, b, K0, c0, hBC⟩ := base_exists u hchild hnj (s + n) (app l ρ) (app σ Z) hX hs0
      (fun e => by rw [show s + n + e = s + (n + e) by omega]; exact hno (n + e))
    have hend := (base_run u hchild (app l ρ) i0 b K0 c0 hBC (app σ Z) hX (s + n) hs0).2
    have hK0ne : K0 ≠ 1 := hBC.2.2.2.2
    have hc0X : ¬ Tower (app c0 (app σ Z)) := app_nontower _ _ hX
    match K0, hK0ne, hend with
    | 0, _, hend => exact hno (n + i0 + 1) (by rw [show s + (n + i0 + 1) = s + n + i0 + 1 by omega]; exact hend)
    | 1, hne, _ => exact hne rfl
    | 2, _, hend =>
      have e2 : Fw (app σ Z) c0 2 = app (app σ Z) (app c0 (app σ Z)) := rfl
      rw [e2] at hend
      obtain ⟨k, _, hk, _⟩ := gamma_walk u hchild hnj _ σ Z _ hend hZ hc0X
      exact hσ ⟨k + 1, hk⟩
    | 3, _, hend =>
      have e3 : Fw (app σ Z) c0 3 = app (app c0 (app σ Z)) (app (app σ Z) (app c0 (app σ Z))) := rfl
      rw [e3] at hend
      have hXc : ¬ Tower (app (app σ Z) (app c0 (app σ Z))) := app_nontower _ _ hc0X
      obtain ⟨k, hk2, hk, hnext⟩ := gamma_walk u hchild hnj _ c0 (app σ Z) _ hend hX hXc
      match k, hk2, hk, hnext with
      | 0, _, hk, hnext =>
        exact no_SS_letter u hchild hnj _ (app σ Z) (app σ Z) hX (by rw [hnext, hk]; rfl)
      | 1, _, _, hnext =>
        have e4 : Fw (app (app σ Z) (app c0 (app σ Z))) (app σ Z) 1 =
            app (app σ Z) (app (app σ Z) (app c0 (app σ Z))) := rfl
        rw [e4] at hnext
        obtain ⟨k1, _, hk1, _⟩ := gamma_walk u hchild hnj _ σ Z _ hnext hZ hXc
        exact hσ ⟨k1 + 1, hk1⟩
      | 2, _, _, hnext =>
        have e4 : Fw (app (app σ Z) (app c0 (app σ Z))) (app σ Z) 2 =
            app (app (app σ Z) (app c0 (app σ Z))) (app (app σ Z) (app (app σ Z) (app c0 (app σ Z)))) := rfl
        rw [e4] at hnext
        obtain ⟨k1, _, hk1, _⟩ := gamma_walk u hchild hnj _ (app σ Z) _ _ hnext hc0X (app_nontower _ _ hXc)
        exact hX ⟨k1 + 1, hk1⟩
    | K + 4, _, hend =>
      have hnt : ∀ i, ¬ Tower (Fw (app σ Z) c0 i) := fun i => SA3.fw_nontower _ c0 hX i
      have e : Fw (app σ Z) c0 (K + 4) =
          app (app (Fw (app σ Z) c0 K) (Fw (app σ Z) c0 (K + 1))) (Fw (app σ Z) c0 (K + 3)) := by
        rw [show K + 4 = (K + 2) + 2 by omega, Fw_add2, Fw_add2]
      rw [e] at hend
      obtain ⟨k1, _, hk1, _⟩ := gamma_walk u hchild hnj _ _ _ _ hend (hnt (K + 1)) (hnt (K + 3))
      exact hnt K ⟨k1 + 1, hk1⟩
  · obtain ⟨k, _, hk, hnext⟩ := gamma_walk u hchild hnj (s + n) l ρ (app σ Z) hs0 hρ hX
    match k, hk, hnext with
    | 0, _, hnext => exact hno (n + 1) (by rw [show s + (n + 1) = s + n + 1 by omega]; exact hnext)
    | 1, hk, _ => exact hYn ρ (by rw [hk])
    | 2, _, hnext =>
      have e5 : Fw (app σ Z) ρ 2 = app (app σ Z) (app ρ (app σ Z)) := rfl
      rw [e5] at hnext
      obtain ⟨k1, _, hk1, _⟩ := gamma_walk u hchild hnj _ σ Z _ hnext hZ (app_nontower _ _ hX)
      exact hσ ⟨k1 + 1, hk1⟩
    | k + 3, _, _ => omega

/-- **A K = 3 step leads to a generalized Omega cycle.**  In a jump-free infinite leftmost walk, a computed step from
    q.σ (σ a non-tower) with H(q) = S (tw 3) c is followed, after finitely many steps, by a monotone walk: c is S(SS)
    (reading lemma, no_SS_letter), the walk must come back to σ.(S(SS).σ) (no_escape), and from there copy_monotone
    applies (the letter S(SS) over σ is a jump node, never visited). -/
theorem K3_monotone (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t : Nat) (q σ c : T) (hu : u t = app q σ)
    (hσ : ¬ Tower σ) (hq : 2 ≤ (args q).length) (hK : Reach (args q) [tw 3, c]) :
    ∃ t2, ∀ e, 3 ≤ (args (u (t2 + e))).length ∧ u (t2 + e + 1) ≠ SA.rpart (u (t2 + e)) := by
  have h1 := fib_next u hchild t q σ c 3 hσ hq hu hK
  have e1 : Fw σ c 3 = app (app c σ) (app σ (app c σ)) := rfl
  rw [e1] at h1
  have hcσ : ¬ Tower (app c σ) := app_nontower _ _ hσ
  have hσcσ : ¬ Tower (app σ (app c σ)) := app_nontower _ _ hcσ
  obtain ⟨k, hk2, hk, hnext⟩ := gamma_walk u hchild hnj (t + 1) c σ _ h1 hσ hσcσ
  match k, hk2, hk, hnext with
  | 0, _, hk, hnext =>
    exact (no_SS_letter u hchild hnj (t + 1 + 1) σ σ hσ (by rw [hnext, hk]; rfl)).elim
  | 2, _, _, hnext =>
    have e2 : Fw (app σ (app c σ)) σ 2 = app (app σ (app c σ)) (app σ (app σ (app c σ))) := rfl
    rw [e2] at hnext
    obtain ⟨k1, _, hk1, _⟩ := gamma_walk u hchild hnj _ σ (app c σ) _ hnext hcσ (app_nontower _ _ hσcσ)
    exact (hσ ⟨k1 + 1, hk1⟩).elim
  | 1, _, hk, hnext =>
    have e2 : Fw (app σ (app c σ)) σ 1 = app σ (app σ (app c σ)) := rfl
    rw [e2] at hnext
    -- the walk comes back to σ.(c.σ)
    have hback : ∃ e, u (t + 1 + 1 + e) = app σ (app c σ) := by
      refine Classical.byContradiction (fun hno => ?_)
      exact no_escape u hchild hnj (t + 1 + 1) σ (app c σ) hσ hcσ hnext
        (fun e he => hno ⟨e, he⟩)
    obtain ⟨e0, he0⟩ := hback
    refine ⟨t + 1 + 1 + e0, copy_monotone u hchild hnj (t + 1 + 1 + e0) σ c he0 hσ (fun e he => ?_)⟩
    exact hnj _ (tw 1) σ (by rw [he, hk]; rfl)

theorem last_le (f : Nat → Nat) (d T : Nat) (hT : f T ≤ d) :
    ∀ M, T < M → (∀ j, M ≤ j → d < f j) → ∃ t, T ≤ t ∧ f t ≤ d ∧ ∀ e, d < f (t + 1 + e) := by
  intro M
  induction M with
  | zero => intro h; omega
  | succ M ih =>
    intro hTM hM
    by_cases hfM : f M ≤ d
    · refine ⟨M, by omega, hfM, fun e => hM _ (by omega)⟩
    · by_cases hTM' : T < M
      · exact ih hTM' (fun j hj => by
          rcases Nat.lt_or_ge j (M + 1) with h | h
          · have : j = M := by omega
            subst this; omega
          · exact hM j h)
      · have : T = M := by omega
        subst this; exact absurd hT hfM

/-- **EM_deep, up to non-tower stacks.**  A jump-free infinite leftmost walk whose right-spine depth tends to infinity
    and whose stacks (last arguments) are eventually non-towers is eventually monotone.  Proof: the last time t >= T
    at which the depth is <= depth (u T) is a strict cut; its step is a K >= 2 Fibonacci step; K = 2: cut_monotone;
    K = 3: K3_monotone; K >= 4 contradicts the reading lemma. -/
theorem EM_deep_nt (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ)
    (hdeep : ∀ d, ∃ N, ∀ j, N ≤ j → d < SA2.msl (u j))
    (hnt : ∃ T, ∀ t, T ≤ t → ¬ Tower (SA.rpart (u t))) :
    ∃ j0, ∀ j, j0 ≤ j → 3 ≤ (args (u j)).length ∧ u (j + 1) ≠ SA.rpart (u j) := by
  obtain ⟨T, hT⟩ := hnt
  obtain ⟨N, hN⟩ := hdeep (SA2.msl (u T))
  obtain ⟨t, htT, htd, hcut⟩ := last_le (fun j => SA2.msl (u j)) (SA2.msl (u T)) T (Nat.le_refl _) (T + N + 1)
    (by omega) (fun j hj => hN j (by omega))
  have htd' : SA2.msl (u t) ≤ SA2.msl (u T) := htd
  have hcut' : ∀ e, SA2.msl (u t) < SA2.msl (u (t + 1 + e)) := fun e => by
    have h : SA2.msl (u T) < SA2.msl (u (t + 1 + e)) := hcut e
    omega
  -- the step at t goes up
  have hσ := hT t htT
  have hc := hchild t
  match hut : u t with
  | S => rw [hut] at hc; exact absurd hc (CA.no_child_S _)
  | app q σ =>
    rw [hut] at hc hσ hcut'
    simp only [SA.rpart] at hσ
    rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, dd, hrr⟩
    · exfalso
      rw [args_app] at hlen hrr
      match hq : args q, hlen, hrr with
      | [], _, hrr =>
        simp only [List.nil_append, List.cons.injEq] at hrr
        have := hcut' 0
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
      have hup := hcut' 0
      rw [Nat.add_zero, hm] at hup
      simp only [SA2.msl] at hup
      match K, hK, hch with
      | 0, _, _ => omega
      | 1, _, _ => omega
      | 2, hK, _ =>
        exact ⟨t, fun j hj => by
          have := cut_monotone u hchild hnj t q σ c hut hσ hq2 hK (by rw [hut]; exact hcut') (j - t)
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

/-- **The leftmost finite half for flag 0 from (J) and (NT).**  An infinite leftmost walk from an L36-flag-0 term is
    impossible if (J) it makes only finitely many jumps and (NT) when its depth tends to infinity its stacks are
    eventually non-towers.  (Scenario A: CA.depth_to_infinity; deep walks: EM_deep_nt; monotone walks:
    EM.finite_half_of_EM.) -/
theorem finite_half_of_J_NT (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hflag : FH.flag (u 0) = false)
    (hJ : ∃ N, ∀ j, N ≤ j → ∀ p τ, u j ≠ app (app S p) τ)
    (hNT : (∀ d, ∃ N, ∀ j, N ≤ j → d < SA2.msl (u j)) → ∃ T, ∀ t, T ≤ t → ¬ Tower (SA.rpart (u t))) :
    False := by
  apply CA.finite_half_of_J_EMdeep u hchild hflag hJ
  intro hdeep
  obtain ⟨N, hN⟩ := hJ
  obtain ⟨T0, hT0⟩ := hNT hdeep
  let v : Nat → T := fun j => u (N + j)
  have hv : ∀ j, FH.LChild (v j) (v (j + 1)) := fun j => by
    show FH.LChild (u (N + j)) (u (N + (j + 1)))
    rw [show N + (j + 1) = N + j + 1 by omega]; exact hchild (N + j)
  have hvnj : ∀ j p τ, v j ≠ app (app S p) τ := fun j p τ => hN (N + j) (by omega) p τ
  have hvdeep : ∀ d, ∃ M, ∀ j, M ≤ j → d < SA2.msl (v j) := by
    intro d
    obtain ⟨M, hM⟩ := hdeep d
    exact ⟨M, fun j hj => hM (N + j) (by omega)⟩
  obtain ⟨j0, hj0⟩ := EM_deep_nt v hv hvnj hvdeep ⟨T0, fun t ht => hT0 (N + t) (by omega)⟩
  refine ⟨N + j0, fun j hj => ?_⟩
  have h := hj0 (j - N) (by omega)
  have h1 : 3 ≤ (args (u (N + (j - N)))).length ∧ u (N + (j - N + 1)) ≠ SA.rpart (u (N + (j - N))) := h
  rw [show N + (j - N) = j by omega, show N + (j - N + 1) = j + 1 by omega] at h1
  exact h1

end SC

#print axioms SC.copy_monotone
#print axioms SC.no_escape
#print axioms SC.K3_monotone
#print axioms SC.EM_deep_nt
#print axioms SC.finite_half_of_J_NT
