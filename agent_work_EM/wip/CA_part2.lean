
/-- **Typed return chains end in T2** (no flag hypothesis).  If H(Q k) = S (X k) (Q (k+1)) and every X k is typed
    (T1-T4), then from some index on every X k is T2 (H(X k) = S S y). -/
theorem chain_T2 (Q X : Nat → T) (hQ : ∀ k, Reach (args (Q k)) [X k, Q (k + 1)])
    (hX : ∀ k, Typed (X k)) : ∃ K, ∀ k, K ≤ k → ∃ y, R (X k) y := by
  have hlen2 : ∀ k, 2 ≤ (args (Q k)).length := by
    intro k
    refine Classical.byContradiction (fun hn => ?_)
    have e := reach_stuck _ _ (by omega) (hQ k)
    have := congrArg List.length e
    simp at this; omega
  have h2step : ∀ k, (args (Q k)).length = 2 → args (Q k) = [X k, Q (k + 1)] := by
    intro k h
    exact (reach_stuck _ _ (by omega) (hQ k)).symm
  have hk1 : ∃ k1, 3 ≤ (args (Q k1)).length := by
    refine Classical.byContradiction (fun hn => ?_)
    have hall : ∀ k, (args (Q k)).length = 2 := fun k => by
      have := hlen2 k
      have : ¬ 3 ≤ (args (Q k)).length := fun h => hn ⟨k, h⟩
      omega
    have hdec : ∀ k, size (Q (k + 1)) < size (Q k) := by
      intro k
      have := h2step k (hall k)
      exact size_args _ _ (by rw [this]; simp)
    have hb : ∀ k, size (Q k) + k ≤ size (Q 0) := by
      intro k; induction k with
      | zero => simp
      | succ k ih => have := hdec k; omega
    have := hb (size (Q 0)); have := size_pos (Q (size (Q 0))); omega
  obtain ⟨k1, hk1⟩ := hk1
  have h3next : ∀ k, 3 ≤ (args (Q k)).length → 3 ≤ (args (Q (k + 1))).length := by
    intro k h3
    refine Classical.byContradiction (fun hn => ?_)
    have hl : (args (Q (k + 1))).length = 2 := by have := hlen2 (k + 1); omega
    obtain ⟨b, hb⟩ := final_app _ _ _ h3 (hQ k)
    have e := h2step (k + 1) hl
    rw [hb, args_app] at e
    have hlast : Q (k + 2) = X k := by
      have := congrArg List.getLast? e
      simp at this
      exact this.symm
    exact typed_dead (Q (k + 2)) (X (k + 2)) (Q (k + 3)) (by rw [hlast]; exact hX k) (hQ (k + 2))
      (hX (k + 2)) (hlen2 (k + 3))
  have h3all : ∀ m, 3 ≤ (args (Q (k1 + m))).length := by
    intro m; induction m with
    | zero => exact hk1
    | succ m ih => exact h3next (k1 + m) ih
  have h3all' : ∀ k, k1 ≤ k → 3 ≤ (args (Q k)).length := by
    intro k hk
    have := h3all (k - k1)
    rwa [show k1 + (k - k1) = k by omega] at this
  have hdec : ∀ k, k1 ≤ k → Q (k + 1) = app (lchild (Q (k + 1))) (X k) ∧
      2 ≤ (args (lchild (Q (k + 1)))).length := by
    intro k hk
    obtain ⟨b, hb⟩ := final_app _ _ _ (h3all' k hk) (hQ k)
    have h3 := h3all' (k + 1) (by omega)
    rw [hb] at h3 ⊢
    refine ⟨rfl, ?_⟩
    simp only [lchild]
    rw [args_app] at h3; simp at h3; omega
  have hst : ∀ k, k1 ≤ k → (X (k + 1) = X k ∧ R (lchild (Q (k + 1))) (lchild (Q (k + 2)))) ∨
      (X k = app S S ∧ X (k + 1) = app S (app S S)) ∨ (∃ y, R (X (k + 1)) y) := by
    intro k hk
    obtain ⟨he, hP⟩ := hdec k hk
    have hr := hQ (k + 1)
    rw [he] at hr
    rcases step_types _ _ _ _ hP (hX k) hr (hX (k + 1)) with ⟨e1, y, hy, e2⟩ | h | h
    · left
      refine ⟨e1, ?_⟩
      have : lchild (Q (k + 2)) = y := by
        show lchild (Q (k + 1 + 1)) = y
        rw [e2]; rfl
      rw [this]; exact hy
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have habs : ∀ k, k1 ≤ k → (∃ y, R (X k) y) → ∃ y, R (X (k + 1)) y := by
    intro k hk ⟨y, hy⟩
    rcases hst k hk with ⟨e1, _⟩ | ⟨e1, _⟩ | h
    · exact ⟨y, e1 ▸ hy⟩
    · exfalso; rw [e1] at hy
      have := reach_stuck _ _ (by simp [args]) hy; simp [args] at this
    · exact h
  refine Classical.byContradiction (fun hn => ?_)
  have hnT2 : ∀ k, k1 ≤ k → ¬ ∃ y, R (X k) y := by
    intro k hk hT
    apply hn
    refine ⟨k, fun m hm => ?_⟩
    have hgo : ∀ e, ∃ y, R (X (k + e)) y := by
      intro e; induction e with
      | zero => exact hT
      | succ e ih => exact habs (k + e) (by omega) ih
    have := hgo (m - k)
    rwa [show k + (m - k) = m by omega] at this
  have hst2 : ∀ k, k1 ≤ k → (X (k + 1) = X k ∧ R (lchild (Q (k + 1))) (lchild (Q (k + 2)))) ∨
      (X k = app S S ∧ X (k + 1) = app S (app S S)) := by
    intro k hk
    rcases hst k hk with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hnT2 (k + 1) (by omega))
  have hk2 : ∃ k2, k1 ≤ k2 ∧ ∀ m, R (lchild (Q (k2 + m + 1))) (lchild (Q (k2 + m + 2))) := by
    by_cases hex : ∃ k, k1 ≤ k ∧ X k ≠ app S S
    · obtain ⟨k, hk, hne⟩ := hex
      have hconst : ∀ m, X (k + m) = X k := by
        intro m; induction m with
        | zero => rfl
        | succ m ih =>
          rcases hst2 (k + m) (by omega) with ⟨e, _⟩ | ⟨e, _⟩
          · rw [show k + (m + 1) = k + m + 1 by omega, e, ih]
          · exact absurd (ih.symm.trans e) hne
      refine ⟨k, hk, fun m => ?_⟩
      rcases hst2 (k + m) (by omega) with ⟨_, hR⟩ | ⟨e, _⟩
      · exact hR
      · exact absurd ((hconst m).symm.trans e) hne
    · have hall : ∀ k, k1 ≤ k → X k = app S S := fun k hk =>
        Classical.byContradiction (fun h => hex ⟨k, hk, h⟩)
      refine ⟨k1, Nat.le_refl _, fun m => ?_⟩
      rcases hst2 (k1 + m) (by omega) with ⟨_, hR⟩ | ⟨_, e⟩
      · exact hR
      · exfalso
        have := hall (k1 + m + 1) (by omega)
        rw [this] at e
        cases e
  obtain ⟨k2, _, hR⟩ := hk2
  exact no_R_chain (fun m => lchild (Q (k2 + m + 1))) (fun m => by
    show R (lchild (Q (k2 + m + 1))) (lchild (Q (k2 + (m + 1) + 1)))
    rw [show k2 + (m + 1) + 1 = k2 + m + 2 by omega]
    exact hR m)

/-- **Case (a') of Conjecture EM is impossible for flag 0.**  No jump-free infinite leftmost walk from a term whose
    L36 class has flag 0 returns infinitely often to nodes q.S. -/
theorem no_caseA (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hflag : FH.flag (u 0) = false) (hnj : ∀ j p τ, u j ≠ app (app S p) τ)
    (hret : ∀ N, ∃ j, N ≤ j ∧ ∃ q, u j = app q S) : False := by
  have hstep : ∀ p : Nat × T, ∃ t : T × T × Nat, u p.1 = app p.2 S →
      Reach (args p.2) [t.1, t.2.1] ∧ u t.2.2 = app t.2.1 S ∧ Typed t.1 := by
    intro p
    by_cases hp : u p.1 = app p.2 S
    · obtain ⟨x0, c0, r', hr, _, hu, hcase⟩ := SA4.return_types_S u hchild hnj hret p.1 p.2 hp
      refine ⟨(x0, c0, r'), fun _ => ⟨hr, hu, ?_⟩⟩
      rcases hcase with ⟨h, _⟩ | ⟨h, _⟩ | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · exact ⟨(S, S, 0), fun h => absurd h hp⟩
  let F : Nat × T → T × T × Nat := fun p => Classical.choose (hstep p)
  have hF : ∀ p, u p.1 = app p.2 S →
      Reach (args p.2) [(F p).1, (F p).2.1] ∧ u (F p).2.2 = app (F p).2.1 S ∧ Typed (F p).1 :=
    fun p => Classical.choose_spec (hstep p)
  let G : Nat × T → Nat × T := fun p => ((F p).2.2, (F p).2.1)
  obtain ⟨r0, _, q0, hq0⟩ := hret 0
  let sq : Nat → Nat × T := SA.iter G (r0, q0)
  have hsq : ∀ k, u (sq k).1 = app (sq k).2 S := by
    intro k; induction k with
    | zero => exact hq0
    | succ k ih => exact (hF (sq k) ih).2.1
  obtain ⟨K, hK⟩ := chain_T2 (fun k => (sq k).2) (fun k => (F (sq k)).1)
    (fun k => (hF (sq k) (hsq k)).1) (fun k => (hF (sq k) (hsq k)).2.2)
  have hclaim : ∀ j, ∃ k, K ≤ k ∧ u ((sq K).1 + j) = app (sq k).2 S := by
    intro j; induction j with
    | zero => exact ⟨K, Nat.le_refl _, hsq K⟩
    | succ j ih =>
      obtain ⟨k, hk, hu⟩ := ih
      obtain ⟨x0, c0, r', hr, _, _, hcase⟩ := SA4.return_types_S u hchild hnj hret _ _ hu
      have e := RC.reach_det _ _ _ hr (hF (sq k) (hsq k)).1 (by simp) (by simp)
      simp only [List.cons.injEq] at e
      obtain ⟨rfl, rfl, _⟩ := e
      obtain ⟨y, hy⟩ := hK k hk
      refine ⟨k + 1, by omega, ?_⟩
      rcases hcase with ⟨_, h⟩ | ⟨_, h⟩ | h | ⟨_, c1, hc1⟩
      · exact h
      · exact h
      · exfalso
        have hy' : R (app S (app S S)) y := by rw [← h]; exact hy
        have := reach_stuck _ _ (by simp [args]) hy'; simp [args] at this
      · exfalso
        rw [args_app] at hc1
        have := SA3.child_S _ S (app S S) c1 y hc1 hy
        cases this
  apply SA4.caseA_needs_T34 u hchild hflag hnj hret
  refine ⟨(sq K).1, fun r q hr hq x0 c0 hx => Or.inr ?_⟩
  obtain ⟨k, hk, hu⟩ := hclaim (r - (sq K).1)
  rw [show (sq K).1 + (r - (sq K).1) = r by omega, hq] at hu
  simp only [app.injEq] at hu
  rw [hu.1] at hx
  have e := RC.reach_det _ _ _ hx (hF (sq k) (hsq k)).1 (by simp) (by simp)
  simp only [List.cons.injEq] at e
  rw [e.1]
  exact hK k hk

end CA

#print axioms CA.step_types
#print axioms CA.typed_dead
#print axioms CA.chain_T2
#print axioms CA.no_caseA
