
namespace SC

open C
open C.T
open FM
open DP

theorem msl_tw : ∀ k, SA2.msl (tw k) = k
  | 0 => rfl
  | k + 1 => by simp only [tw, SA2.msl, msl_tw k]

/-- the second component of H(Q.z) has z as a right-spine suffix -/
theorem snd_suf (Q z x2 c2 : T) (hQ : 1 ≤ (args Q).length) (h : Reach (args (app Q z)) [x2, c2]) :
    Suf z c2 := by
  rw [args_app] at h
  by_cases h3 : 3 ≤ (args Q ++ [z]).length
  · obtain ⟨b, hb⟩ := final_app _ _ _ h3 h
    have hs := first_suf z (args Q ++ [z]) _ ⟨args Q, z, rfl, Suf.refl⟩ h3 h x2 c2 rfl
    rw [hb]; exact Suf.wrap _ _ hs
  · have e := reach_stuck _ _ (by omega) h
    match hq : args Q, e with
    | [p], e =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
      rw [e.2.1]; exact Suf.refl
    | [], _ => rw [hq] at hQ; simp at hQ
    | _ :: _ :: _, _ => rw [hq] at h3; simp at h3

/-- the child of y.Z (y with >= 2 args) is Z itself (an R-step) or has the suffix (snd H y).Z -/
theorem child_suf (y Z c dd : T) (hy : 2 ≤ (args y).length) (h : Reach (args (app y Z)) [c, dd]) :
    ∃ x0 c0, Reach (args y) [x0, c0] ∧ (c = Z ∨ Suf (app c0 Z) c) := by
  rw [args_app] at h
  rcases OM.cinv2_reach y Z hy _ h with ⟨L1, _, hlen1, hEq⟩ | ⟨x, c1, w', P, _, _, _, hlen1, hEq⟩ |
      ⟨x, c', w', b, _, hH, _, hEq⟩ | ⟨y', hr, hEq⟩
  · have := congrArg List.length hEq; simp at this; omega
  · have := congrArg List.length hEq; simp at this; omega
  · simp only [List.cons.injEq] at hEq
    obtain ⟨hc', _, _⟩ := hEq
    obtain ⟨x0, c0, hq0, hcase⟩ := SA3.wh_c0 y Z x c' w' hH
    refine ⟨x0, c0, hq0, Or.inr ?_⟩
    rw [hc']
    rcases hcase with ⟨hw, hcc⟩ | hs
    · rw [hw, hcc]; exact Suf.refl
    · exact Suf.wrap _ _ hs
  · simp only [List.cons.injEq] at hEq
    exact ⟨S, y', hr, Or.inl hEq.1⟩

/-- a right-spine suffix of the same depth is the term itself -/
theorem suf_msl_eq (A B : T) (h : Suf A B) (hm : SA2.msl A = SA2.msl B) : A = B := by
  cases B with
  | S => exact suf_S A h
  | app p x =>
    rcases suf_app_inv A p x h with h1 | h1
    · exact h1.symm
    · have := SA2.msl_suf _ _ h1
      simp only [SA2.msl] at hm
      omega

/-- **(NT') holds.**  In a jump-free infinite leftmost walk whose depth tends to infinity, after any time N there is a
    strict cut whose stack is a non-tower.  (A strict cut on a tower stack is an S-push node (S x S).(tw m)
    (tower_cut_S); the tops met afterwards at depth m+2 all have tw m as a right-spine suffix (child_suf, snd_suf), so
    the last visit to depth m+2 cannot be an S-push node again; tower_cut_S then yields a non-tower strict cut.) -/
theorem NT_holds (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ)
    (hdeep : ∀ d, ∃ N, ∀ j, N ≤ j → d < SA2.msl (u j)) (N : Nat) :
    ∃ t, N ≤ t ∧ ¬ Tower (SA.rpart (u t)) ∧ ∀ e, SA2.msl (u t) < SA2.msl (u (t + 1 + e)) := by
  -- a late strict cut t0 of depth >= 3
  obtain ⟨N2, hN2⟩ := hdeep 2
  obtain ⟨N3, hN3⟩ := hdeep (SA2.msl (u (N + N2)))
  obtain ⟨t0, ht0T, ht0d, ht0cut⟩ := last_le (fun j => SA2.msl (u j)) (SA2.msl (u (N + N2))) (N + N2)
    (Nat.le_refl _) (N + N2 + N3 + 1) (by omega) (fun j hj => hN3 j (by omega))
  have hd0 : SA2.msl (u t0) ≤ SA2.msl (u (N + N2)) := ht0d
  have hcut0 : ∀ e, SA2.msl (u t0) < SA2.msl (u (t0 + 1 + e)) := fun e => by
    have h : SA2.msl (u (N + N2)) < SA2.msl (u (t0 + 1 + e)) := ht0cut e
    omega
  have h3 : 2 < SA2.msl (u t0) := hN2 t0 (by omega)
  by_cases hnt0 : ¬ Tower (SA.rpart (u t0))
  · exact ⟨t0, by omega, hnt0, hcut0⟩
  have htw0 : Tower (SA.rpart (u t0)) := Classical.byContradiction hnt0
  obtain ⟨m, hm⟩ := htw0
  match hut0 : u t0 with
  | S => rw [hut0] at h3; simp [SA2.msl] at h3
  | app q σ =>
    rw [hut0] at hm h3 hcut0
    simp only [SA.rpart] at hm
    subst hm
    have hmsl0 : SA2.msl (app q (tw m)) = m + 1 := by simp only [SA2.msl, msl_tw]
    have hm2 : 2 ≤ m := by rw [hmsl0] at h3; omega
    have hcut0' : ∀ e, SA2.msl (u t0) < SA2.msl (u (t0 + 1 + e)) := by rw [hut0]; exact hcut0
    rcases tower_cut_S u hchild hnj hdeep t0 m q hut0 hcut0' with ⟨t', ht', hnt', hcut'⟩ | ⟨x, hqx, _⟩
    · exact ⟨t', by omega, hnt', hcut'⟩
    subst hqx
    -- the child of (S x S).(tw m) is the child of the virtual node x.(tw m).(tw (m+1))
    have hc := hchild t0
    rw [hut0] at hc
    rcases hc with ⟨hlen, _, _⟩ | ⟨_, dd, hrr⟩
    · exfalso; simp [args] at hlen
    have hstep : step (args (app (app (app S x) S) (tw m))) =
        some (args (app (app x (tw m)) (tw (m + 1)))) := by
      simp [args, step, tw, List.append_assoc]
    have hrr2 : Reach (args (app (app x (tw m)) (tw (m + 1)))) [u (t0 + 1), dd] := by
      rcases RC.reach_head _ _ hrr with h | ⟨X', hX', hr'⟩
      · exfalso; have := congrArg List.length h; simp [args] at this
      · rw [hstep] at hX'
        simp only [Option.some.injEq] at hX'
        rw [hX']; exact hr'
    have hmsl1 : m + 2 ≤ SA2.msl (u (t0 + 1)) := by
      have := hcut0' 0; rw [Nat.add_zero, hut0, hmsl0] at this; omega
    -- x /= S
    have hx1 : 1 ≤ (args x).length := by
      by_cases hxS : x = S
      · exfalso
        subst hxS
        have e := reach_stuck _ _ (by simp [args]) hrr2
        have e1 : u (t0 + 1) = tw m := by
          have := congrArg List.head? e
          simpa [args] using this
        rw [e1] at hmsl1
        simp only [msl_tw] at hmsl1
        omega
      · exact TC.args_ne_nil x hxS
    have hxm2 : 2 ≤ (args (app x (tw m))).length := by rw [args_app]; simp; omega
    obtain ⟨x2, c2, hc2, hcase⟩ := child_suf (app x (tw m)) (tw (m + 1)) _ dd hxm2 hrr2
    have hW : Suf (app c2 (tw (m + 1))) (u (t0 + 1)) := by
      rcases hcase with h | h
      · exfalso; rw [h, msl_tw] at hmsl1; omega
      · exact h
    have htm_c2 : Suf (tw m) c2 := snd_suf x (tw m) x2 c2 hx1 hc2
    -- the walk never goes below depth m+2 after t0
    have hge : ∀ e, m + 2 ≤ SA2.msl (u (t0 + 1 + e)) := fun e => by
      have := hcut0' e; rw [hut0, hmsl0] at this; omega
    -- invariant: the spine node at depth m+2 is y.(tw (m+1)) with tw m a suffix of y
    have hinv : ∀ e, ∃ y, Suf (tw m) y ∧ Suf (app y (tw (m + 1))) (u (t0 + 1 + e)) := by
      intro e
      induction e with
      | zero => exact ⟨c2, htm_c2, hW⟩
      | succ e ih =>
        obtain ⟨y, hty, hsy⟩ := ih
        rw [show t0 + 1 + (e + 1) = t0 + 1 + e + 1 by omega]
        by_cases hne : u (t0 + 1 + e) = app y (tw (m + 1))
        · -- a visit to depth m+2: the next top is snd H(y)
          have hc' := hchild (t0 + 1 + e)
          rw [hne] at hc'
          rcases hc' with ⟨hlen', rest', hrr'⟩ | ⟨hlen', dd', hrr'⟩
          · exfalso
            rw [args_app] at hlen' hrr'
            match hy : args y, hlen', hrr' with
            | [], _, hrr' =>
              simp only [List.nil_append, List.cons.injEq] at hrr'
              have := hge (e + 1)
              rw [show t0 + 1 + (e + 1) = t0 + 1 + e + 1 by omega, ← hrr'.1, msl_tw] at this
              omega
            | [p], _, _ => exact hnj (t0 + 1 + e) p _ (by rw [hne, TC.args_one' y p hy])
            | _ :: _ :: _, hlen', _ => simp at hlen'
          · rw [args_app] at hlen'
            have hy2 : 2 ≤ (args y).length := by simp at hlen'; omega
            obtain ⟨x0, c0, hq0, hcase'⟩ := child_suf y (tw (m + 1)) _ dd' hy2 hrr'
            rcases hcase' with h | h
            · exfalso
              have := hge (e + 1)
              rw [show t0 + 1 + (e + 1) = t0 + 1 + e + 1 by omega, h, msl_tw] at this
              omega
            · refine ⟨c0, ?_, h⟩
              -- tw m is a suffix of the last argument of y, hence of c0
              match y, hy2, hq0, hty with
              | S, hy2, _, _ => simp [args] at hy2
              | app Q z, hy2, hq0, hty =>
                have hQ1 : 1 ≤ (args Q).length := by rw [args_app] at hy2; simp at hy2; omega
                have hz : Suf z c0 := snd_suf Q z x0 c0 hQ1 hq0
                rcases suf_app_inv _ Q z hty with h1 | h1
                · exfalso
                  have hle := SA.args_tw_le m
                  rw [← h1] at hle
                  omega
                · exact suf_trans _ _ _ h1 hz
        · exact ⟨y, hty, SA.step_keeps _ _ _ (hchild (t0 + 1 + e)) hsy (Ne.symm (Ne.symm hne)) (hnj _)⟩
    -- c2 /= S, so W is a non-tower
    have hc2S : c2 ≠ S := by
      intro h; rw [h] at htm_c2; have := suf_S _ htm_c2
      cases m with
      | zero => omega
      | succ m' => cases this
    by_cases hvisit : ∃ s, SA2.msl (u (t0 + 1 + s)) = m + 2
    · -- the last visit to depth m+2 is a strict cut on the tower stack tw (m+1)
      obtain ⟨s0, hs0⟩ := hvisit
      obtain ⟨M4, hM4⟩ := hdeep (m + 2)
      obtain ⟨t1, ht1s, ht1d, ht1cut⟩ := last_le (fun j => SA2.msl (u j)) (m + 2) (t0 + 1 + s0)
        (by show SA2.msl (u (t0 + 1 + s0)) ≤ m + 2; omega) (t0 + 1 + s0 + M4 + 1) (by omega)
        (fun j hj => hM4 j (by omega))
      have hd1 : SA2.msl (u t1) ≤ m + 2 := ht1d
      have hge1 : m + 2 ≤ SA2.msl (u t1) := by
        have := hge (t1 - (t0 + 1)); rwa [show t0 + 1 + (t1 - (t0 + 1)) = t1 by omega] at this
      obtain ⟨y, hty, hsy⟩ := hinv (t1 - (t0 + 1))
      rw [show t0 + 1 + (t1 - (t0 + 1)) = t1 by omega] at hsy
      have hut1 : u t1 = app y (tw (m + 1)) := by
        refine (suf_msl_eq _ _ hsy ?_).symm
        simp only [SA2.msl, msl_tw]; omega
      have hcut1 : ∀ e, SA2.msl (u t1) < SA2.msl (u (t1 + 1 + e)) := fun e => by
        have h : m + 2 < SA2.msl (u (t1 + 1 + e)) := ht1cut e
        omega
      rcases tower_cut_S u hchild hnj hdeep t1 (m + 1) y hut1 hcut1 with ⟨t', ht', hnt', hcut'⟩ | ⟨x', hyx, _⟩
      · exact ⟨t', by omega, hnt', hcut'⟩
      · exfalso
        rw [hyx] at hty
        rcases suf_app_inv _ _ _ hty with h1 | h1
        · cases m with
          | zero => omega
          | succ m' => simp [tw] at h1
        · have := suf_S _ h1
          cases m with
          | zero => omega
          | succ m' => cases this
    · -- the walk never returns to depth m+2: W = c2.(tw (m+1)) is a frozen non-tower
      have hnov : ∀ s, m + 2 < SA2.msl (u (t0 + 1 + s)) := fun s => by
        have := hge s
        rcases Nat.lt_or_ge (m + 2) (SA2.msl (u (t0 + 1 + s))) with h | h
        · exact h
        · exact absurd ⟨s, by omega⟩ hvisit
      have hWnt : ¬ Tower (app c2 (tw (m + 1))) := by
        rintro ⟨k, hk⟩
        cases k with
        | zero => cases hk
        | succ k => simp only [tw, app.injEq] at hk; exact hc2S hk.1
      have hfrz : ∀ e, Suf (app c2 (tw (m + 1))) (u (t0 + 1 + e)) ∧ u (t0 + 1 + e) ≠ app c2 (tw (m + 1)) := by
        intro e
        induction e with
        | zero =>
          refine ⟨hW, fun h => ?_⟩
          have := hnov 0; rw [h] at this; simp only [SA2.msl, msl_tw] at this; omega
        | succ e ih =>
          refine ⟨?_, fun h => ?_⟩
          · rw [show t0 + 1 + (e + 1) = t0 + 1 + e + 1 by omega]
            exact SA.step_keeps _ _ _ (hchild (t0 + 1 + e)) ih.1 ih.2 (hnj (t0 + 1 + e))
          · have := hnov (e + 1); rw [h] at this; simp only [SA2.msl, msl_tw] at this; omega
      obtain ⟨M5, hM5⟩ := hdeep (SA2.msl (u (t0 + 1)))
      obtain ⟨t', ht'T, ht'd, ht'cut⟩ := last_le (fun j => SA2.msl (u j)) (SA2.msl (u (t0 + 1))) (t0 + 1)
        (Nat.le_refl _) (t0 + 1 + M5 + 1) (by omega) (fun j hj => hM5 j (by omega))
      have hd' : SA2.msl (u t') ≤ SA2.msl (u (t0 + 1)) := ht'd
      refine ⟨t', by omega, ?_, fun e => by
        have h : SA2.msl (u (t0 + 1)) < SA2.msl (u (t' + 1 + e)) := ht'cut e
        omega⟩
      obtain ⟨hs', hne'⟩ := hfrz (t' - (t0 + 1))
      rw [show t0 + 1 + (t' - (t0 + 1)) = t' by omega] at hs' hne'
      match hut' : u t' with
      | S => rw [hut'] at hs'; exact absurd (suf_S _ hs') (by intro h; cases h)
      | app a b =>
        rw [hut'] at hs' hne'
        simp only [SA.rpart]
        rcases suf_app_inv _ a b hs' with h | h
        · exact absurd h hne'
        · exact suf_nontower _ _ h hWnt

/-- **EM_deep (MACHINE-CHECKED).**  Every jump-free infinite leftmost walk whose right-spine depth tends to infinity
    is eventually monotone. -/
theorem EM_deep (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ)
    (hdeep : ∀ d, ∃ N, ∀ j, N ≤ j → d < SA2.msl (u j)) :
    ∃ j0, ∀ j, j0 ≤ j → 3 ≤ (args (u j)).length ∧ u (j + 1) ≠ SA.rpart (u j) := by
  obtain ⟨t, _, hσ, hcut⟩ := NT_holds u hchild hnj hdeep 0
  exact EM_of_cut u hchild hnj t hσ hcut

/-- **The leftmost finite half for flag 0 from (J) alone.**  An infinite leftmost walk from a term whose L36 class has
    flag 0 must make infinitely many jumps (nodes S p τ).  Equivalently: if every infinite leftmost walk makes only
    finitely many jumps (Conjecture J), then every flag-0 term has a finite leftmost Böhm path, and L36 decides
    leftmost-path finiteness. -/
theorem finite_half_of_J (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hflag : FH.flag (u 0) = false)
    (hJ : ∃ N, ∀ j, N ≤ j → ∀ p τ, u j ≠ app (app S p) τ) : False := by
  apply CA.finite_half_of_J_EMdeep u hchild hflag hJ
  intro hdeep
  obtain ⟨N, hN⟩ := hJ
  let v : Nat → T := fun j => u (N + j)
  have hv : ∀ j, FH.LChild (v j) (v (j + 1)) := fun j => by
    show FH.LChild (u (N + j)) (u (N + (j + 1)))
    rw [show N + (j + 1) = N + j + 1 by omega]; exact hchild (N + j)
  have hvnj : ∀ j p τ, v j ≠ app (app S p) τ := fun j p τ => hN (N + j) (by omega) p τ
  have hvdeep : ∀ d, ∃ M, ∀ j, M ≤ j → d < SA2.msl (v j) := by
    intro d
    obtain ⟨M, hM⟩ := hdeep d
    exact ⟨M, fun j hj => hM (N + j) (by omega)⟩
  obtain ⟨j0, hj0⟩ := EM_deep v hv hvnj hvdeep
  refine ⟨N + j0, fun j hj => ?_⟩
  have h := hj0 (j - N) (by omega)
  have h1 : 3 ≤ (args (u (N + (j - N)))).length ∧ u (N + (j - N + 1)) ≠ SA.rpart (u (N + (j - N))) := h
  rw [show N + (j - N) = j by omega, show N + (j - N + 1) = j + 1 by omega] at h1
  exact h1

end SC

#print axioms SC.NT_holds
#print axioms SC.EM_deep
#print axioms SC.finite_half_of_J
