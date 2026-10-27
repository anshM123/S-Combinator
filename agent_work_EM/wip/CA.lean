import EMBase

/-! ## Case (a') of Conjecture EM: typed return chains end in T2 — CA (agent_work_EM, 2026-10-27) -/

namespace CA

open C
open C.T
open FM

/-- the four return-step types of SA4.return_types_S: T1 SS, T2 H(x) = S S y, T3 S(SS),
    T4 (>= 2 args and H(x.S) = S (SS) c1) -/
def Typed (x : T) : Prop :=
  x = app S S ∨ (∃ y, R x y) ∨ x = app S (app S S) ∨
  (2 ≤ (args x).length ∧ ∃ c1, Reach (args (app x S)) [app S S, c1])

theorem not_typed_S : ¬ Typed S := by
  rintro (h | ⟨y, hy⟩ | h | ⟨h2, _⟩)
  · cases h
  · exact R_S y hy
  · cases h
  · simp [args] at h2

/-- (L4) a T4 term is S x' S -/
theorem T4_shape (x c1 : T) (h2 : 2 ≤ (args x).length) (h : Reach (args (app x S)) [app S S, c1]) :
    ∃ x', args x = [x', S] := by
  rw [args_app] at h
  rcases OM.cinv2_reach x S h2 _ h with ⟨L1, _, hlen, hEq⟩ | ⟨x1, c, w, P, _, _, _, hlen, hEq⟩ |
      ⟨x1, c, w, b, _, hH, _, hEq⟩ | ⟨y, _, hEq⟩
  · have := congrArg List.length hEq; simp at this; omega
  · have := congrArg List.length hEq; simp at this; omega
  · simp only [List.cons.injEq, app.injEq] at hEq
    obtain ⟨⟨rfl, rfl⟩, _⟩ := hEq
    cases hH with
    | first _ _ hr =>
      by_cases h3 : 3 ≤ (args x).length
      · obtain ⟨b', hb'⟩ := final_app _ _ _ h3 hr
        cases hb'
      · have := reach_stuck _ _ (by omega) hr
        exact ⟨x1, this.symm⟩
  · simp only [List.cons.injEq] at hEq
    exact absurd hEq.1 (by intro h; cases h)

/-- (L3) a typed term is never a chain element followed by a typed step to a multiplier with >= 2 args -/
theorem typed_dead (q x q' : T) (hT : Typed q) (h : Reach (args q) [x, q']) (hx : Typed x)
    (h2 : 2 ≤ (args q').length) : False := by
  rcases hT with rfl | ⟨y, hy⟩ | rfl | ⟨h2q, c1, hc1⟩
  · have := reach_stuck _ _ (by simp [args]) h; simp [args] at this
  · have e := RC.reach_det _ _ _ h hy (by simp) (by simp)
    simp only [List.cons.injEq] at e
    obtain ⟨rfl, _⟩ := e
    exact not_typed_S hx
  · have := reach_stuck _ _ (by simp [args]) h; simp [args] at this
  · obtain ⟨x', hx'⟩ := T4_shape q c1 h2q hc1
    rw [hx'] at h
    have := reach_stuck _ _ (by simp) h
    simp only [List.cons.injEq] at this
    obtain ⟨_, rfl, _⟩ := this
    simp [args] at h2

theorem size_two (z : T) (hz : z ≠ S) (h : size z ≤ 2) : z = app S S := by
  cases z with
  | S => exact absurd rfl hz
  | app a b =>
    simp only [size] at h
    have ha := size_pos a; have hb := size_pos b
    rw [OM.size_le_one a (by omega), OM.size_le_one b (by omega)]

/-- (L1 + L2) a typed step from P.z (P with >= 2 args, z typed): an R-step on P keeping z, the wrap SS -> S(SS), or a
    step to a T2 term -/
theorem step_types (P z x' q'' : T) (hP : 2 ≤ (args P).length) (hz : Typed z)
    (h : Reach (args (app P z)) [x', q'']) (hx : Typed x') :
    (x' = z ∧ ∃ y, R P y ∧ q'' = app y z) ∨ (z = app S S ∧ x' = app S (app S S)) ∨ (∃ y, R x' y) := by
  rw [args_app] at h
  rcases OM.cinv2_reach P z hP _ h with ⟨L1, _, hlen, hEq⟩ | ⟨x1, c, w, Pl, _, _, _, hlen, hEq⟩ |
      ⟨x1, c, w, b, _, hH, _, hEq⟩ | ⟨y, hr, hEq⟩
  · have := congrArg List.length hEq; simp at this; omega
  · have := congrArg List.length hEq; simp at this; omega
  · simp only [List.cons.injEq] at hEq
    obtain ⟨hx'cw, _, _⟩ := hEq
    have hsz := OM.wh_size _ _ _ _ _ hH
    have hzS : z ≠ S := fun e => not_typed_S (e ▸ hz)
    subst hx'cw
    rcases hx with h1 | ⟨y, hy⟩ | h3 | ⟨h2, c1, hc1⟩
    · simp only [app.injEq] at h1
      obtain ⟨_, rfl⟩ := h1
      exact absurd (OM.size_le_one z (by simpa [size] using hsz)) hzS
    · exact Or.inr (Or.inr ⟨y, hy⟩)
    · simp only [app.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      exact Or.inr (Or.inl ⟨size_two z hzS (by simpa [size] using hsz), rfl⟩)
    · obtain ⟨x'', hx''⟩ := T4_shape _ c1 h2 hc1
      rw [args_app] at hx''
      have hw : w = S := by
        have := congrArg List.getLast? hx''
        simpa using this
      subst hw
      exact absurd (OM.size_le_one z (by simpa [size] using hsz)) hzS
  · simp only [List.cons.injEq] at hEq
    exact Or.inl ⟨hEq.1, y, hr, hEq.2.1⟩


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
