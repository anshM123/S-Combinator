
namespace SC

open C
open C.T
open FM
open DP

theorem twr2_tw2_nontower (Y : T) : ¬ Tower (app (tw 2) Y) := by
  rintro ⟨m, hm⟩
  cases m with
  | zero => cases hm
  | succ m =>
    simp only [tw, app.injEq] at hm
    exact absurd hm.1 (by intro h; cases h)

/-- **Strict cut at a K = 2 step ⇒ the walk is a generalized Omega cycle from then on.**  In a jump-free infinite
    leftmost walk, let t be a time whose node q.σ (σ a non-tower) makes a K = 2 step (H(q) = S (S(SS)) c) and after
    which the depth never comes back to the level of u t.  Then from t on every node has >= 3 arguments and no child
    is the node's last argument (eventually monotone).  Proof: σ = S(SS)^n Y; the copy is read (tw2_skips); Y cannot
    be a tower, an SS- or S(S(SS))-headed letter over a non-tower (strict cut, no_tw3_push), so Y has a tower last
    argument and starts a base program (base_exists); its final step cannot return (strict cut), K = 3 and K >= 4 die
    (reading lemma, no_SS_letter), so it is a CALL; the reading lemma at the first two CALLs forces c = c0 = S(SS)
    (no_SS_letter, no_tw3_push), and then the cycle invariant (cyc_forever) holds forever. -/
theorem cut_monotone (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t : Nat) (q σ c : T) (hu : u t = app q σ)
    (hσ : ¬ Tower σ) (hq : 2 ≤ (args q).length) (hK : Reach (args q) [tw 2, c])
    (hcut : ∀ e, SA2.msl (u t) < SA2.msl (u (t + 1 + e))) :
    ∀ e, 3 ≤ (args (u (t + e))).length ∧ u (t + e + 1) ≠ SA.rpart (u (t + e)) := by
  have h1 : u (t + 1) = app σ (app c σ) := fib_next u hchild t q σ c 2 hσ hq hu hK
  have hcσ : ¬ Tower (app c σ) := app_nontower c σ hσ
  have hnoX : ∀ e, u (t + 1 + e) ≠ app c σ := by
    intro e h
    have h2 := hcut e
    rw [h, hu] at h2
    simp only [SA2.msl] at h2
    omega
  obtain ⟨n, Y, hσY, hYn⟩ := twr2_decomp σ
  -- Y is not a tower
  have hY : ¬ Tower Y := by
    rintro ⟨mY, hmY⟩
    cases n with
    | zero => exact hσ ⟨mY, by rw [hσY, hmY]; rfl⟩
    | succ n1 =>
      have hs := tw2_skips u hchild hnj (app (tw 2) Y) (app c σ) (twr2_tw2_nontower Y) hcσ n1 (t + 1)
        (by rw [h1, hσY, Twr2_shift])
      have hb2 : 2 ≤ (args (app (tw 2) Y)).length := by simp [args, tw]
      have hr : Reach (args (app (tw 2) Y)) [tw 1, Y] := Reach.refl
      have h2 := fib_next u hchild (t + 1 + n1) (app (tw 2) Y) (app c σ) Y 1 hcσ hb2 hs hr
      have e1 : Fw (app c σ) Y 1 = app Y (app c σ) := rfl
      rw [e1, hmY] at h2
      cases mY with
      | zero =>
        have hc2 := hchild (t + 1 + n1 + 1)
        rw [h2] at hc2
        rcases hc2 with ⟨_, rest, hrr⟩ | ⟨hlen, _, _⟩
        · simp only [tw, args, List.nil_append, List.cons.injEq] at hrr
          exact hnoX (n1 + 2) (by rw [show t + 1 + (n1 + 2) = t + 1 + n1 + 1 + 1 by omega]; exact hrr.1.symm)
        · simp [args, tw] at hlen
      | succ m1 => exact hnj _ (tw m1) (app c σ) h2
  have hs0 : u (t + 1 + n) = app Y (app c σ) :=
    tw2_skips u hchild hnj Y (app c σ) hY hcσ n (t + 1) (by rw [h1, hσY])
  -- Y = l.ρ
  match Y, hY, hYn, hσY, hs0 with
  | S, hY, _, _, _ => exact absurd ⟨0, rfl⟩ hY
  | app l ρ, hY, hYn, hσY, hs0 =>
  by_cases hρ : Tower ρ
  · -- the base program
    obtain ⟨i0, b, K0, c0, hBC⟩ := base_exists u hchild hnj (t + 1 + n) (app l ρ) (app c σ) hcσ hs0
      (fun e => by rw [show t + 1 + n + e = t + 1 + (n + e) by omega]; exact hnoX (n + e))
    obtain ⟨hrun, hend⟩ := base_run u hchild (app l ρ) i0 b K0 c0 hBC (app c σ) hcσ (t + 1 + n) hs0
    have hK0ne : K0 ≠ 1 := hBC.2.2.2.2
    have hlast : Reach (args (b i0)) [tw K0, c0] := hBC.2.2.2.1
    have hcall : u (t + 1 + n + i0) = app (b i0) (app c σ) := hrun i0 (Nat.le_refl _)
    match K0, hK0ne, hlast, hend with
    | 0, _, _, hend =>
      exact absurd hend (by rw [show t + 1 + n + i0 + 1 = t + 1 + (n + i0 + 1) by omega]; exact hnoX _)
    | 1, hne, _, _ => exact absurd rfl hne
    | 2, _, hlast, hend =>
      -- first CALL: the reading lemma at the copy c.σ
      have e2 : Fw (app c σ) c0 2 = app (app c σ) (app c0 (app c σ)) := rfl
      rw [e2] at hend
      have hc0X : ¬ Tower (app c0 (app c σ)) := app_nontower _ _ hcσ
      obtain ⟨k, hk2, hk, hnext⟩ := gamma_walk u hchild hnj _ c σ _ hend hσ hc0X
      match k, hk2, hk, hnext with
      | 0, _, hk, _ =>
        exact (no_SS_letter u hchild hnj (t + 1) σ σ hσ (by rw [h1, hk]; rfl)).elim
      | 2, _, hk, _ =>
        exact (no_tw3_push u hchild hnj (t + 1 + n + i0) (b i0) c0 σ 0 hσ (by rw [hcall, hk]; rfl)
          hBC.2.2.1 hlast).elim
      | 1, _, hk, hnext =>
        -- c = S(SS); the second CALL forces c0 = S(SS)
        have e3 : Fw (app c0 (app c σ)) σ 1 = app σ (app c0 (app c σ)) := rfl
        rw [e3] at hnext
        have hs1 := tw2_skips u hchild hnj (app l ρ) (app c0 (app c σ)) hY hc0X n _ (by rw [hnext, hσY])
        have hrun2 := base_run u hchild (app l ρ) i0 b 2 c0 hBC (app c0 (app c σ)) hc0X _ hs1
        have hend2 := hrun2.2
        have hcall2 := hrun2.1 i0 (Nat.le_refl _)
        have e4 : Fw (app c0 (app c σ)) c0 2 = app (app c0 (app c σ)) (app c0 (app c0 (app c σ))) := rfl
        rw [e4] at hend2
        obtain ⟨k2, hk22, hk2', _⟩ := gamma_walk u hchild hnj _ c0 (app c σ) _ hend2 hcσ (app_nontower _ _ hc0X)
        match k2, hk22, hk2' with
        | 0, _, hk2' =>
          exact (no_SS_letter u hchild hnj (t + 1 + n + i0 + 1) (app c σ) (app c σ) hcσ
            (by rw [hend, hk2']; rfl)).elim
        | 2, _, hk2' =>
          exact (no_tw3_push u hchild hnj _ (b i0) c0 (app c σ) 0 hcσ (by rw [hcall2, hk2']; rfl)
            hBC.2.2.1 hlast).elim
        | 1, _, hk2' =>
          -- c = c0 = S(SS): the cycle invariant holds at t+1
          have hBC' : BaseChain (app l ρ) i0 b 2 (tw 2) := by rw [← hk2']; exact hBC
          have hI : CycInv (app l ρ) i0 b (u (t + 1)) := by
            rw [h1, hσY, hk]
            cases n with
            | zero => exact ⟨0, Or.inr ⟨0, Nat.zero_le _, by rw [hBC.1]; rfl⟩⟩
            | succ n1 => exact ⟨n1 + 1, Or.inl ⟨n1 + 1, by omega, Nat.le_refl _, rfl⟩⟩
          have hmono := cyc_forever u hchild hnj (app l ρ) hY i0 b hBC' (t + 1) hI
          intro e
          cases e with
          | zero =>
            show 3 ≤ (args (u t)).length ∧ u (t + 1) ≠ SA.rpart (u t)
            refine ⟨by rw [hu, args_app]; simp; omega, ?_⟩
            rw [h1, hu]; simp only [SA.rpart]
            intro h
            have h2 := congrArg size h
            have h3 : size (app σ (app c σ)) = size σ + size (app c σ) := rfl
            have h4 := size_pos (app c σ)
            omega
          | succ e1 =>
            have := hmono e1
            rw [show t + 1 + e1 = t + (e1 + 1) by omega] at this
            exact this
    | 3, _, hlast, hend =>
      exfalso
      have e2 : Fw (app c σ) c0 3 = app (app c0 (app c σ)) (app (app c σ) (app c0 (app c σ))) := rfl
      rw [e2] at hend
      have hc0X : ¬ Tower (app c0 (app c σ)) := app_nontower _ _ hcσ
      have hXc0X : ¬ Tower (app (app c σ) (app c0 (app c σ))) := app_nontower _ _ hc0X
      obtain ⟨k, hk2, hk, hnext⟩ := gamma_walk u hchild hnj _ c0 (app c σ) _ hend hcσ hXc0X
      match k, hk2, hk, hnext with
      | 0, _, hk, hnext =>
        exact no_SS_letter u hchild hnj _ (app c σ) (app c σ) hcσ (by rw [hnext, hk]; rfl)
      | 2, _, _, hnext =>
        obtain ⟨k3, _, hk3, _⟩ := gamma_walk u hchild hnj _ (app c σ) _ _ hnext hc0X (app_nontower _ _ hXc0X)
        exact hcσ ⟨k3 + 1, hk3⟩
      | 1, _, hk, hnext =>
        have e3 : Fw (app (app c σ) (app c0 (app c σ))) (app c σ) 1 =
            app (app c σ) (app (app c σ) (app c0 (app c σ))) := rfl
        rw [e3] at hnext
        obtain ⟨k1, hk12, hk1, hnext2⟩ := gamma_walk u hchild hnj _ c σ _ hnext hσ hXc0X
        match k1, hk12, hk1, hnext2 with
        | 0, _, hk1, _ => exact no_SS_letter u hchild hnj (t + 1) σ σ hσ (by rw [h1, hk1]; rfl)
        | 2, _, _, hnext2 =>
          obtain ⟨k3, _, hk3, _⟩ := gamma_walk u hchild hnj _ (app c σ) _ _ hnext2
            hc0X (app_nontower _ _ hXc0X)
          exact hcσ ⟨k3 + 1, hk3⟩
        | 1, _, _, hnext2 =>
          have e4 : Fw (app (app c σ) (app c0 (app c σ))) σ 1 =
              app σ (app (app c σ) (app c0 (app c σ))) := rfl
          rw [e4] at hnext2
          have hs2 := tw2_skips u hchild hnj (app l ρ) _ hY hXc0X n _ (by rw [hnext2, hσY])
          have hend3 := (base_run u hchild (app l ρ) i0 b 3 c0 hBC _ hXc0X _ hs2).2
          have e5 : ∀ W : T, Fw W c0 3 = app (app c0 W) (app W (app c0 W)) := fun W => rfl
          rw [e5] at hend3
          obtain ⟨k4, _, hk4, hnext4⟩ := gamma_walk u hchild hnj _ c0 _ _ hend3 hXc0X
            (app_nontower _ _ (app_nontower _ _ hXc0X))
          have hk4' : k4 = 1 := by
            have := SA3.tw_inj (k4 + 1) 2 (by rw [← hk4, hk])
            omega
          subst hk4'
          have e6 : ∀ W : T, Fw (app W (app c0 W)) W 1 = app W (app W (app c0 W)) := fun W => rfl
          rw [e6] at hnext4
          obtain ⟨k5, _, hk5, _⟩ := gamma_walk u hchild hnj _ (app c σ) (app c0 (app c σ)) _
            hnext4 hc0X (app_nontower _ _ (app_nontower _ _ hXc0X))
          exact hcσ ⟨k5 + 1, hk5⟩
    | K + 4, _, _, hend =>
      exfalso
      have hnt : ∀ i, ¬ Tower (Fw (app c σ) c0 i) := fun i => SA3.fw_nontower _ c0 hcσ i
      have e : Fw (app c σ) c0 (K + 4) =
          app (app (Fw (app c σ) c0 K) (Fw (app c σ) c0 (K + 1))) (Fw (app c σ) c0 (K + 3)) := by
        rw [show K + 4 = (K + 2) + 2 by omega, Fw_add2, Fw_add2]
      rw [e] at hend
      obtain ⟨k1, _, hk1, _⟩ := gamma_walk u hchild hnj _ _ _ _ hend (hnt (K + 1)) (hnt (K + 3))
      exact hnt K ⟨k1 + 1, hk1⟩
  · -- ρ is a non-tower: the reading lemma at Y.(c.σ)
    exfalso
    obtain ⟨k, _, hk, hnext⟩ := gamma_walk u hchild hnj (t + 1 + n) l ρ (app c σ) hs0 hρ hcσ
    match k, hk, hnext with
    | 0, _, hnext => exact hnoX (n + 1) (by rw [show t + 1 + (n + 1) = t + 1 + n + 1 by omega]; exact hnext)
    | 1, hk, _ => exact hYn ρ (by rw [hk])
    | 2, hk, _ =>
      exact no_tw3_push u hchild hnj t q c ρ n hρ (by rw [hu, hσY, hk]) hq hK
    | k + 3, _, _ => omega

theorem copy_monotone (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t1 : Nat) (σ c : T)
    (h1 : u t1 = app σ (app c σ)) (hσ : ¬ Tower σ) (hnoX : ∀ e, u (t1 + e) ≠ app c σ) :
    ∀ e, 3 ≤ (args (u (t1 + e))).length ∧ u (t1 + e + 1) ≠ SA.rpart (u (t1 + e)) := by
  have hcσ : ¬ Tower (app c σ) := app_nontower c σ hσ
  obtain ⟨n, Y, hσY, hYn⟩ := twr2_decomp σ
  -- Y is not a tower
  have hY : ¬ Tower Y := by
    rintro ⟨mY, hmY⟩
    cases n with
    | zero => exact hσ ⟨mY, by rw [hσY, hmY]; rfl⟩
    | succ n1 =>
      have hs := tw2_skips u hchild hnj (app (tw 2) Y) (app c σ) (twr2_tw2_nontower Y) hcσ n1 (t1)
        (by rw [h1, hσY, Twr2_shift])
      have hb2 : 2 ≤ (args (app (tw 2) Y)).length := by simp [args, tw]
      have hr : Reach (args (app (tw 2) Y)) [tw 1, Y] := Reach.refl
      have h2 := fib_next u hchild (t1 + n1) (app (tw 2) Y) (app c σ) Y 1 hcσ hb2 hs hr
      have e1 : Fw (app c σ) Y 1 = app Y (app c σ) := rfl
      rw [e1, hmY] at h2
      cases mY with
      | zero =>
        have hc2 := hchild (t1 + n1 + 1)
        rw [h2] at hc2
        rcases hc2 with ⟨_, rest, hrr⟩ | ⟨hlen, _, _⟩
        · simp only [tw, args, List.nil_append, List.cons.injEq] at hrr
          exact hnoX (n1 + 2) (by rw [show t1 + (n1 + 2) = t1 + n1 + 1 + 1 by omega]; exact hrr.1.symm)
        · simp [args, tw] at hlen
      | succ m1 => exact hnj _ (tw m1) (app c σ) h2
  have hs0 : u (t1 + n) = app Y (app c σ) :=
    tw2_skips u hchild hnj Y (app c σ) hY hcσ n (t1) (by rw [h1, hσY])
  -- Y = l.ρ
  match Y, hY, hYn, hσY, hs0 with
  | S, hY, _, _, _ => exact absurd ⟨0, rfl⟩ hY
  | app l ρ, hY, hYn, hσY, hs0 =>
  by_cases hρ : Tower ρ
  · -- the base program
    obtain ⟨i0, b, K0, c0, hBC⟩ := base_exists u hchild hnj (t1 + n) (app l ρ) (app c σ) hcσ hs0
      (fun e => by rw [show t1 + n + e = t1 + (n + e) by omega]; exact hnoX (n + e))
    obtain ⟨hrun, hend⟩ := base_run u hchild (app l ρ) i0 b K0 c0 hBC (app c σ) hcσ (t1 + n) hs0
    have hK0ne : K0 ≠ 1 := hBC.2.2.2.2
    have hlast : Reach (args (b i0)) [tw K0, c0] := hBC.2.2.2.1
    have hcall : u (t1 + n + i0) = app (b i0) (app c σ) := hrun i0 (Nat.le_refl _)
    match K0, hK0ne, hlast, hend with
    | 0, _, _, hend =>
      exact absurd hend (by rw [show t1 + n + i0 + 1 = t1 + (n + i0 + 1) by omega]; exact hnoX _)
    | 1, hne, _, _ => exact absurd rfl hne
    | 2, _, hlast, hend =>
      -- first CALL: the reading lemma at the copy c.σ
      have e2 : Fw (app c σ) c0 2 = app (app c σ) (app c0 (app c σ)) := rfl
      rw [e2] at hend
      have hc0X : ¬ Tower (app c0 (app c σ)) := app_nontower _ _ hcσ
      obtain ⟨k, hk2, hk, hnext⟩ := gamma_walk u hchild hnj _ c σ _ hend hσ hc0X
      match k, hk2, hk, hnext with
      | 0, _, hk, _ =>
        exact (no_SS_letter u hchild hnj (t1) σ σ hσ (by rw [h1, hk]; rfl)).elim
      | 2, _, hk, _ =>
        exact (no_tw3_push u hchild hnj (t1 + n + i0) (b i0) c0 σ 0 hσ (by rw [hcall, hk]; rfl)
          hBC.2.2.1 hlast).elim
      | 1, _, hk, hnext =>
        -- c = S(SS); the second CALL forces c0 = S(SS)
        have e3 : Fw (app c0 (app c σ)) σ 1 = app σ (app c0 (app c σ)) := rfl
        rw [e3] at hnext
        have hs1 := tw2_skips u hchild hnj (app l ρ) (app c0 (app c σ)) hY hc0X n _ (by rw [hnext, hσY])
        have hrun2 := base_run u hchild (app l ρ) i0 b 2 c0 hBC (app c0 (app c σ)) hc0X _ hs1
        have hend2 := hrun2.2
        have hcall2 := hrun2.1 i0 (Nat.le_refl _)
        have e4 : Fw (app c0 (app c σ)) c0 2 = app (app c0 (app c σ)) (app c0 (app c0 (app c σ))) := rfl
        rw [e4] at hend2
        obtain ⟨k2, hk22, hk2', _⟩ := gamma_walk u hchild hnj _ c0 (app c σ) _ hend2 hcσ (app_nontower _ _ hc0X)
        match k2, hk22, hk2' with
        | 0, _, hk2' =>
          exact (no_SS_letter u hchild hnj (t1 + n + i0 + 1) (app c σ) (app c σ) hcσ
            (by rw [hend, hk2']; rfl)).elim
        | 2, _, hk2' =>
          exact (no_tw3_push u hchild hnj _ (b i0) c0 (app c σ) 0 hcσ (by rw [hcall2, hk2']; rfl)
            hBC.2.2.1 hlast).elim
        | 1, _, hk2' =>
          -- c = c0 = S(SS): the cycle invariant holds at t+1
          have hBC' : BaseChain (app l ρ) i0 b 2 (tw 2) := by rw [← hk2']; exact hBC
          have hI : CycInv (app l ρ) i0 b (u (t1)) := by
            rw [h1, hσY, hk]
            cases n with
            | zero => exact ⟨0, Or.inr ⟨0, Nat.zero_le _, by rw [hBC.1]; rfl⟩⟩
            | succ n1 => exact ⟨n1 + 1, Or.inl ⟨n1 + 1, by omega, Nat.le_refl _, rfl⟩⟩
          have hmono := cyc_forever u hchild hnj (app l ρ) hY i0 b hBC' (t1) hI
          exact hmono
    | 3, _, hlast, hend =>
      exfalso
      have e2 : Fw (app c σ) c0 3 = app (app c0 (app c σ)) (app (app c σ) (app c0 (app c σ))) := rfl
      rw [e2] at hend
      have hc0X : ¬ Tower (app c0 (app c σ)) := app_nontower _ _ hcσ
      have hXc0X : ¬ Tower (app (app c σ) (app c0 (app c σ))) := app_nontower _ _ hc0X
      obtain ⟨k, hk2, hk, hnext⟩ := gamma_walk u hchild hnj _ c0 (app c σ) _ hend hcσ hXc0X
      match k, hk2, hk, hnext with
      | 0, _, hk, hnext =>
        exact no_SS_letter u hchild hnj _ (app c σ) (app c σ) hcσ (by rw [hnext, hk]; rfl)
      | 2, _, _, hnext =>
        obtain ⟨k3, _, hk3, _⟩ := gamma_walk u hchild hnj _ (app c σ) _ _ hnext hc0X (app_nontower _ _ hXc0X)
        exact hcσ ⟨k3 + 1, hk3⟩
      | 1, _, hk, hnext =>
        have e3 : Fw (app (app c σ) (app c0 (app c σ))) (app c σ) 1 =
            app (app c σ) (app (app c σ) (app c0 (app c σ))) := rfl
        rw [e3] at hnext
        obtain ⟨k1, hk12, hk1, hnext2⟩ := gamma_walk u hchild hnj _ c σ _ hnext hσ hXc0X
        match k1, hk12, hk1, hnext2 with
        | 0, _, hk1, _ => exact no_SS_letter u hchild hnj (t1) σ σ hσ (by rw [h1, hk1]; rfl)
        | 2, _, _, hnext2 =>
          obtain ⟨k3, _, hk3, _⟩ := gamma_walk u hchild hnj _ (app c σ) _ _ hnext2
            hc0X (app_nontower _ _ hXc0X)
          exact hcσ ⟨k3 + 1, hk3⟩
        | 1, _, _, hnext2 =>
          have e4 : Fw (app (app c σ) (app c0 (app c σ))) σ 1 =
              app σ (app (app c σ) (app c0 (app c σ))) := rfl
          rw [e4] at hnext2
          have hs2 := tw2_skips u hchild hnj (app l ρ) _ hY hXc0X n _ (by rw [hnext2, hσY])
          have hend3 := (base_run u hchild (app l ρ) i0 b 3 c0 hBC _ hXc0X _ hs2).2
          have e5 : ∀ W : T, Fw W c0 3 = app (app c0 W) (app W (app c0 W)) := fun W => rfl
          rw [e5] at hend3
          obtain ⟨k4, _, hk4, hnext4⟩ := gamma_walk u hchild hnj _ c0 _ _ hend3 hXc0X
            (app_nontower _ _ (app_nontower _ _ hXc0X))
          have hk4' : k4 = 1 := by
            have := SA3.tw_inj (k4 + 1) 2 (by rw [← hk4, hk])
            omega
          subst hk4'
          have e6 : ∀ W : T, Fw (app W (app c0 W)) W 1 = app W (app W (app c0 W)) := fun W => rfl
          rw [e6] at hnext4
          obtain ⟨k5, _, hk5, _⟩ := gamma_walk u hchild hnj _ (app c σ) (app c0 (app c σ)) _
            hnext4 hc0X (app_nontower _ _ (app_nontower _ _ hXc0X))
          exact hcσ ⟨k5 + 1, hk5⟩
    | K + 4, _, _, hend =>
      exfalso
      have hnt : ∀ i, ¬ Tower (Fw (app c σ) c0 i) := fun i => SA3.fw_nontower _ c0 hcσ i
      have e : Fw (app c σ) c0 (K + 4) =
          app (app (Fw (app c σ) c0 K) (Fw (app c σ) c0 (K + 1))) (Fw (app c σ) c0 (K + 3)) := by
        rw [show K + 4 = (K + 2) + 2 by omega, Fw_add2, Fw_add2]
      rw [e] at hend
      obtain ⟨k1, _, hk1, _⟩ := gamma_walk u hchild hnj _ _ _ _ hend (hnt (K + 1)) (hnt (K + 3))
      exact hnt K ⟨k1 + 1, hk1⟩
  · -- ρ is a non-tower: the reading lemma at Y.(c.σ)
    exfalso
    obtain ⟨k, _, hk, hnext⟩ := gamma_walk u hchild hnj (t1 + n) l ρ (app c σ) hs0 hρ hcσ
    match k, hk, hnext with
    | 0, _, hnext => exact hnoX (n + 1) (by rw [show t1 + (n + 1) = t1 + n + 1 by omega]; exact hnext)
    | 1, hk, _ => exact hYn ρ (by rw [hk])
    | 2, hk, hnext =>
      have e7 : Fw (app c σ) ρ 2 = app (app c σ) (app ρ (app c σ)) := rfl
      rw [e7] at hnext
      have hρcσ : ¬ Tower (app ρ (app c σ)) := app_nontower _ _ hcσ
      obtain ⟨k1, hk12, hk1, hnext2⟩ := gamma_walk u hchild hnj _ c σ _ hnext hσ hρcσ
      match k1, hk12, hk1, hnext2 with
      | 0, _, hk1, _ => exact no_SS_letter u hchild hnj t1 σ σ hσ (by rw [h1, hk1]; rfl)
      | 2, _, _, hnext2 =>
        have e8 : Fw (app ρ (app c σ)) σ 2 = app (app ρ (app c σ)) (app σ (app ρ (app c σ))) := rfl
        rw [e8] at hnext2
        obtain ⟨k3, _, hk3, _⟩ := gamma_walk u hchild hnj _ ρ (app c σ) _ hnext2 hcσ (app_nontower _ _ hρcσ)
        exact hρ ⟨k3 + 1, hk3⟩
      | 1, _, _, hnext2 =>
        have e8 : Fw (app ρ (app c σ)) σ 1 = app σ (app ρ (app c σ)) := rfl
        rw [e8] at hnext2
        have hs3 := tw2_skips u hchild hnj (app l ρ) _ hY hρcσ n _ (by rw [hnext2, hσY])
        rw [hk] at hs3
        obtain ⟨k4, _, hk4, hnext4⟩ := gamma_walk u hchild hnj _ (tw 3) ρ _ hs3 hρ hρcσ
        have hk4' : k4 = 2 := by have := SA3.tw_inj 3 (k4 + 1) hk4; omega
        subst hk4'
        have e9 : Fw (app ρ (app c σ)) ρ 2 = app (app ρ (app c σ)) (app ρ (app ρ (app c σ))) := rfl
        rw [e9] at hnext4
        obtain ⟨k5, _, hk5, _⟩ := gamma_walk u hchild hnj _ ρ (app c σ) _ hnext4 hcσ (app_nontower _ _ hρcσ)
        exact hρ ⟨k5 + 1, hk5⟩
    | k + 3, _, _ => omega


end SC

#print axioms SC.cut_monotone
