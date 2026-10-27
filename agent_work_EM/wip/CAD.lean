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

/-! ## The reading lemma for deep jump-free walks — DP (agent_work_EM, 2026-10-27) -/

namespace DP

open C
open C.T
open FM

theorem tower_S : Tower S := ⟨0, rfl⟩

theorem nontower_ne_S (x : T) (h : ¬ Tower x) : x ≠ S := fun e => h (e ▸ tower_S)

/-- **Reading lemma, node form.**  If the head run of the node (A.B).σ (A /= S) reaches a head normal form [ch, d] and
    B, σ are non-towers, then A = tw (k+1) (so H(A.B) = S (tw k) B) and ch = Fw σ B k. -/
theorem gamma_node (A B σ ch d : T) (hA : A ≠ S) (hB : ¬ Tower B) (hσ : ¬ Tower σ)
    (h : Reach (args (app (app A B) σ)) [ch, d]) : ∃ k, A = tw (k + 1) ∧ ch = Fw σ B k := by
  have hA1 := TC.args_ne_nil A hA
  have hQ : 2 ≤ (args (app A B)).length := by rw [args_app]; simp; omega
  obtain ⟨K, c0, hK, hch⟩ := fib_step (app A B) σ ch d hQ hσ h
  rw [args_app] at hK
  by_cases h2 : 2 ≤ (args A).length
  · exfalso
    have hK' : Reach (args (app A B)) [tw K, c0] := by rw [args_app]; exact hK
    obtain ⟨K', c', _, hfw⟩ := fib_step A B (tw K) c0 h2 hB hK'
    exact SA3.fw_nontower B c' hB K' (hfw ▸ ⟨K, rfl⟩)
  · match hax : args A, hA1, h2 with
    | [p], _, _ =>
      rw [hax] at hK
      have e := reach_stuck _ _ (by simp) hK
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
      obtain ⟨hp, hc, _⟩ := e
      refine ⟨K, ?_, ?_⟩
      · rw [TC.args_one' A p hax, ← hp]; rfl
      · rw [hch, ← hc]
    | [], h1, _ => simp at h1
    | _ :: _ :: _, _, h2 => simp at h2

/-- **Reading lemma, walk form.**  In a jump-free infinite leftmost walk, a node (A.B).σ with B and σ non-towers has
    A = tw (k+1) with k <= 2, and its child is σ (k = 0: a return), B.σ (k = 1) or σ.(B.σ) (k = 2). -/
theorem gamma_walk (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t : Nat) (A B σ : T) (hu : u t = app (app A B) σ)
    (hB : ¬ Tower B) (hσ : ¬ Tower σ) : ∃ k, k ≤ 2 ∧ A = tw (k + 1) ∧ u (t + 1) = Fw σ B k := by
  -- a computed node of the walk reaches its child
  have hreach : ∀ j X Y Z, u j = app (app X Y) Z → X ≠ S → ∃ dd, Reach (args (u j)) [u (j + 1), dd] := by
    intro j X Y Z hj hX
    rcases hchild j with ⟨hlen, _, _⟩ | ⟨_, dd, hr⟩
    · exfalso
      rw [hj, args_app, args_app] at hlen
      have h1 := TC.args_ne_nil X hX
      have h2 : (args X ++ [Y] ++ [Z]).length = (args X).length + 2 := by simp
      omega
    · exact ⟨dd, hr⟩
  have hAS : A ≠ S := by intro e; rw [e] at hu; exact hnj t B σ hu
  obtain ⟨dd, hr⟩ := hreach t A B σ hu hAS
  rw [hu] at hr
  obtain ⟨k, hk, hch⟩ := gamma_node A B σ _ dd hAS hB hσ hr
  refine ⟨k, ?_, hk, hch⟩
  refine Classical.byContradiction (fun hk2 => ?_)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  -- the child Fw (m+3) = (X.Y).Z with X, Y, Z non-towers: the reading lemma at t+1 makes X a tower
  have hnt : ∀ i, ¬ Tower (Fw σ B i) := fun i => SA3.fw_nontower σ B hσ i
  obtain ⟨X, Y, hXY, hX, hY⟩ : ∃ X Y, Fw σ B (m + 1) = app X Y ∧ ¬ Tower X ∧ ¬ Tower Y := by
    cases m with
    | zero => exact ⟨B, σ, rfl, hB, hσ⟩
    | succ m' => exact ⟨Fw σ B m', Fw σ B (m' + 1), Fw_add2 σ B m', hnt _, hnt _⟩
  have hu1 : u (t + 1) = app (app X Y) (Fw σ B (m + 2)) := by
    rw [hch, show m + 3 = (m + 1) + 2 by omega, Fw_add2, hXY]
  obtain ⟨dd1, hr1⟩ := hreach (t + 1) X Y _ hu1 (nontower_ne_S X hX)
  rw [hu1] at hr1
  obtain ⟨k1, hk1, _⟩ := gamma_node X Y _ _ dd1 (nontower_ne_S X hX) hY (hnt (m + 2)) hr1
  exact hX ⟨k1 + 1, hk1⟩

end DP

#print axioms DP.gamma_node
#print axioms DP.gamma_walk

namespace DP

open C
open C.T
open FM

/-- **Jump classification over a non-tower bottom.**  If the leftmost child of the node Q.v (Q with >= 2 arguments,
    v a non-tower) is a jump node S p τ, then H(Q) = S (tw K) c0 with
    K = 0: v = S p τ (the walk returned onto a stack level whose multiplier is S p);
    K = 1: c0 = S p and τ = v (a DISCARD jump: the rightmost child of Q is S p, the stack v is dropped);
    K = 2: v = S p and τ = c0.v (the jump target p lies below an S on the stack);
    K = 3: c0 = S and p = v (the jump target is the stack v itself). -/
theorem jump_child (Q v p τ d : T) (hQ : 2 ≤ (args Q).length) (hv : ¬ Tower v)
    (h : Reach (args (app Q v)) [app (app S p) τ, d]) :
    ∃ c0, (Reach (args Q) [tw 0, c0] ∧ v = app (app S p) τ) ∨
      (Reach (args Q) [tw 1, c0] ∧ c0 = app S p ∧ τ = v) ∨
      (Reach (args Q) [tw 2, c0] ∧ v = app S p ∧ τ = app c0 v) ∨
      (Reach (args Q) [tw 3, c0] ∧ c0 = S ∧ p = v) := by
  obtain ⟨K, c0, hK, hch⟩ := fib_step Q v _ d hQ hv h
  refine ⟨c0, ?_⟩
  match K, hK, hch with
  | 0, hK, hch => exact Or.inl ⟨hK, hch.symm⟩
  | 1, hK, hch =>
    have e : Fw v c0 1 = app c0 v := rfl
    rw [e] at hch
    simp only [app.injEq] at hch
    exact Or.inr (Or.inl ⟨hK, hch.1.symm, hch.2⟩)
  | 2, hK, hch =>
    rw [show (2 : Nat) = 0 + 2 from rfl, Fw_add2] at hch
    simp only [app.injEq] at hch
    have e : Fw v c0 (0 + 1) = app c0 v := rfl
    exact Or.inr (Or.inr (Or.inl ⟨hK, hch.1.symm, by rw [← e]; exact hch.2⟩))
  | 3, hK, hch =>
    rw [show (3 : Nat) = 1 + 2 from rfl, Fw_add2] at hch
    simp only [app.injEq] at hch
    have e : Fw v c0 1 = app c0 v := rfl
    rw [e] at hch
    simp only [app.injEq] at hch
    exact Or.inr (Or.inr (Or.inr ⟨hK, hch.1.1.symm, hch.1.2⟩))
  | i + 4, _, hch =>
    exfalso
    rw [show i + 4 = (i + 2) + 2 by omega, Fw_add2, Fw_add2] at hch
    simp only [app.injEq] at hch
    -- Fw v c0 i = S, impossible for a non-tower v
    exact SA3.fw_nontower v c0 hv i (hch.1.1 ▸ tower_S)

end DP

#print axioms DP.jump_child

namespace DP

open C
open C.T
open FM

/-- **Tower letters are frozen.**  In a jump-free leftmost walk, once a stack segment tw (k+1).ρ (a tower letter on
    top of ρ) is a right-spine suffix of a node, it stays a PROPER right-spine suffix of every later node: the node
    tw (k+1).ρ = S (tw k) ρ is a jump node and is never visited, and non-jump steps keep proper suffixes. -/
theorem tower_letter_frozen (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t k : Nat) (ρ : T) (hs : Suf (app (tw (k + 1)) ρ) (u t)) :
    ∀ e, Suf (app (tw (k + 1)) ρ) (u (t + e)) ∧ u (t + e) ≠ app (tw (k + 1)) ρ := by
  have hne : ∀ s, u s ≠ app (tw (k + 1)) ρ := fun s h => hnj s (tw k) ρ (by rw [h]; rfl)
  intro e
  induction e with
  | zero => exact ⟨hs, hne t⟩
  | succ e ih =>
    refine ⟨?_, hne _⟩
    rw [show t + (e + 1) = t + e + 1 by omega]
    exact SA.step_keeps _ _ _ (hchild (t + e)) ih.1 ih.2 (hnj (t + e))

/-- ... and the walk stays strictly above it: the right-spine depth never drops to the level of the tower letter. -/
theorem tower_letter_depth (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t k : Nat) (ρ : T) (hs : Suf (app (tw (k + 1)) ρ) (u t)) :
    ∀ e, SA2.msl (app (tw (k + 1)) ρ) < SA2.msl (u (t + e)) := by
  intro e
  obtain ⟨h1, h2⟩ := tower_letter_frozen u hchild hnj t k ρ hs e
  generalize u (t + e) = x at h1 h2
  cases x with
  | S => exact absurd (suf_S _ h1).symm (by intro h; cases h)
  | app p y =>
    rcases suf_app_inv _ p y h1 with h | h
    · exact absurd h h2
    · have := SA2.msl_suf _ _ h
      simp only [SA2.msl] at this ⊢
      omega

end DP

#print axioms DP.tower_letter_frozen
#print axioms DP.tower_letter_depth

namespace DP

open C
open C.T
open FM

theorem msl_Fw (z c : T) : ∀ i, SA2.msl (Fw z c i) = SA2.msl z + i ∧ SA2.msl (Fw z c (i + 1)) = SA2.msl z + i + 1
  | 0 => ⟨by simp [Fw], by simp [Fw, SA2.msl]⟩
  | i + 1 => by
    have ih := msl_Fw z c i
    refine ⟨by rw [ih.2]; omega, ?_⟩
    rw [show i + 1 + 1 = i + 2 from rfl, Fw_add2]
    simp only [SA2.msl]
    rw [ih.2]; omega

/-- an up-crossing of level d between a and a + n -/
theorem upcross (f : Nat → Nat) (d a : Nat) (ha : f a ≤ d) :
    ∀ n, d < f (a + n) → ∃ p, a ≤ p ∧ p < a + n ∧ f p ≤ d ∧ d < f (p + 1) := by
  intro n
  induction n with
  | zero => intro h; simp at h; omega
  | succ n ih =>
    intro h
    by_cases h2 : d < f (a + n)
    · obtain ⟨p, h1, h3, h4, h5⟩ := ih h2
      exact ⟨p, h1, by omega, h4, h5⟩
    · exact ⟨a + n, by omega, by omega, by omega, by rw [show a + n + 1 = a + (n + 1) by omega]; exact h⟩

/-- **EM_deep from tower pushes (TP).**  Let u be a jump-free infinite leftmost walk whose right-spine depth tends to
    infinity.  Suppose that from some time T on every stack (last argument) is a non-tower and every computed step that
    pushes K >= 2 multipliers is an Omega-type push of a TOWER LETTER: H(q) = S (tw 2) (tw (k+1)).  Then u is
    eventually monotone (no pops, jumps or returns).  Proof: a late return lands at a level d >= depth (u T); some step
    p in [T, r) crosses level d upwards, so it pushes K >= 2, hence a tower letter tw (k+1) at level d, which is
    frozen forever (tower_letter_depth) — the walk can never come back to level d. -/
theorem EM_of_TP (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ)
    (hdeep : ∀ d, ∃ N, ∀ j, N ≤ j → d < SA2.msl (u j)) (T : Nat)
    (hTP : ∀ t, T ≤ t → ¬ Tower (SA.rpart (u t)) ∧
      ∀ q σ K c, u t = app q σ → 2 ≤ (args q).length → Reach (args q) [tw K, c] → 2 ≤ K →
        K = 2 ∧ ∃ k, c = tw (k + 1)) :
    ∃ j0, ∀ j, j0 ≤ j → 3 ≤ (args (u j)).length ∧ u (j + 1) ≠ SA.rpart (u j) := by
  obtain ⟨N, hN⟩ := hdeep (SA2.msl (u T))
  have hnoret : ∀ r, T ≤ r → N ≤ r + 1 → u (r + 1) ≠ SA.rpart (u r) := by
    intro r hTr hNr hret
    have hr1 : SA2.msl (u r) = SA2.msl (u (r + 1)) + 1 := by
      rw [hret]
      match hur : u r with
      | S => exfalso; have := hchild r; rw [hur] at this; exact CA.no_child_S _ this
      | app f x => simp [SA.rpart, SA2.msl]
    have hTd : SA2.msl (u T) ≤ SA2.msl (u (r + 1)) := by have := hN (r + 1) hNr; omega
    obtain ⟨p, hp1, hp2, hp3, hp4⟩ := upcross (fun j => SA2.msl (u j)) (SA2.msl (u (r + 1))) T hTd (r - T)
      (by show SA2.msl (u (r + 1)) < SA2.msl (u (T + (r - T))); rw [show T + (r - T) = r by omega]; omega)
    have hp3' : SA2.msl (u p) ≤ SA2.msl (u (r + 1)) := hp3
    have hp4' : SA2.msl (u (r + 1)) < SA2.msl (u (p + 1)) := hp4
    clear hp3 hp4
    -- analyse the up-going step at p
    match hup : u p with
    | S => exfalso; have := hchild p; rw [hup] at this; exact CA.no_child_S _ this
    | app q σ =>
      have hc := hchild p
      rw [hup] at hc hp3'
      rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, dd, hrr⟩
      · rw [args_app] at hlen hrr
        match hq : args q, hlen, hrr with
        | [], _, hrr =>
          simp only [List.nil_append, List.cons.injEq] at hrr
          rw [← hrr.1] at hp4'
          simp only [SA2.msl] at hp3'
          omega
        | [x], _, _ => exact hnj p x σ (by rw [hup, TC.args_one' q x hq])
        | _ :: _ :: _, hlen, _ => simp at hlen
      · rw [args_app] at hlen
        have hq2 : 2 ≤ (args q).length := by simp at hlen; omega
        have hσ : ¬ Tower σ := by have := (hTP p hp1).1; rw [hup] at this; exact this
        obtain ⟨K, c, hK, hch⟩ := fib_step q σ _ dd hq2 hσ hrr
        have hm := (msl_Fw σ c K).1
        rw [← hch] at hm
        simp only [SA2.msl] at hp3'
        have hK2 : 2 ≤ K := by omega
        obtain ⟨hK2', k, hck⟩ := (hTP p hp1).2 q σ K c hup hq2 hK hK2
        subst hK2'
        -- the tower letter c.σ sits at level msl σ + 1 = msl (u (r+1)) and is frozen from p+1 on
        have hsuf : Suf (app (tw (k + 1)) σ) (u (p + 1)) := by
          rw [hch, ← hck]
          exact Suf.wrap _ _ Suf.refl
        have hfz := tower_letter_depth u hchild hnj (p + 1) k σ hsuf (r - p)
        rw [show p + 1 + (r - p) = r + 1 by omega] at hfz
        simp only [SA2.msl] at hfz
        omega
  refine ⟨T + N, fun j hj => ⟨?_, hnoret j (by omega) (by omega)⟩⟩
  have hc := hchild j
  match huj : u j with
  | S => rw [huj] at hc; exact absurd hc (CA.no_child_S _)
  | app q σ =>
    rw [huj] at hc
    rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, _, _⟩
    · exfalso
      rw [args_app] at hlen hrr
      match hq : args q, hlen, hrr with
      | [], _, hrr =>
        simp only [List.nil_append, List.cons.injEq] at hrr
        apply hnoret j (by omega) (by omega)
        rw [huj, ← hrr.1]; rfl
      | [x], _, _ => exact hnj j x σ (by rw [huj, TC.args_one' q x hq])
      | _ :: _ :: _, hlen, _ => simp at hlen
    · exact hlen

end DP

#print axioms DP.EM_of_TP

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

namespace DP

open C
open C.T
open FM

theorem app_nontower (c Z : T) (hZ : ¬ Tower Z) : ¬ Tower (app c Z) :=
  suf_nontower Z (app c Z) (Suf.wrap c Z Suf.refl) hZ

theorem SS_nontower (ρ : T) : ¬ Tower (app (app S S) ρ) := by
  rintro ⟨m, hm⟩
  cases m with
  | zero => cases hm
  | succ m =>
    simp only [tw, app.injEq] at hm
    exact absurd hm.1 (by intro h; cases h)

theorem tw_eq_one (k : Nat) (h : app S S = tw (k + 1)) : k = 0 := by
  have := SA3.tw_inj 1 (k + 1) h
  omega

/-- **No SS letter on top of the stack.**  In a jump-free infinite leftmost walk no node has the form X.(SS.ρ) with ρ
    a non-tower.  (The segment SS.ρ = S S ρ is a jump node, hence frozen; by the reading lemma every step from a node
    X'.(SS.ρ) comes back to a node X''.(SS.ρ) after one or two steps — a pushed copy whose first letter is SS is read
    and returns at once — or reaches a jump node; so the walk would return infinitely often to the level directly
    above the fixed non-tower SS.ρ, which SA.no_scenarioA excludes.)  Consequence: no step ever pushes the letter SS
    over a non-tower stack (no K = 2 push of SS, no K = 3 push of SS). -/
theorem no_SS_letter (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t : Nat) (X ρ : T) (hρ : ¬ Tower ρ)
    (hu : u t = app X (app (app S S) ρ)) : False := by
  have hZnt : ¬ Tower (app (app S S) ρ) := SS_nontower ρ
  let v : Nat → T := fun j => u (t + j)
  have hv : ∀ j, FH.LChild (v j) (v (j + 1)) := fun j => by
    show FH.LChild (u (t + j)) (u (t + (j + 1)))
    rw [show t + (j + 1) = t + j + 1 by omega]; exact hchild (t + j)
  have hvnj : ∀ j p τ, v j ≠ app (app S p) τ := fun j p τ => hnj (t + j) p τ
  have habove : ∀ j, Suf (app (app S S) ρ) (v j) ∧ v j ≠ app (app S S) ρ := by
    intro j
    exact tower_letter_frozen u hchild hnj t 0 ρ (by rw [hu]; exact Suf.wrap _ _ Suf.refl) j
  have hcZ : ∀ c, ¬ Tower (app c (app (app S S) ρ)) := fun c => app_nontower c _ hZnt
  have hnext : ∀ j X', v j = app X' (app (app S S) ρ) →
      ∃ X'', v (j + 1) = app X'' (app (app S S) ρ) ∨ v (j + 2) = app X'' (app (app S S) ρ) := by
    intro j X' hj
    have hc := hv j
    rw [hj] at hc
    rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, dd, hrr⟩
    · exfalso
      rw [args_app] at hlen hrr
      match hX : args X', hlen, hrr with
      | [], _, hrr =>
        simp only [List.nil_append, List.cons.injEq] at hrr
        exact hvnj (j + 1) S ρ hrr.1.symm
      | [p], _, _ => exact hvnj j p _ (by rw [hj, TC.args_one' X' p hX])
      | _ :: _ :: _, hlen, _ => simp at hlen
    · rw [args_app] at hlen
      have hX2 : 2 ≤ (args X').length := by simp at hlen; omega
      obtain ⟨K, c, _, hch⟩ := fib_step X' _ _ dd hX2 hZnt hrr
      match K, hch with
      | 0, hch => exact absurd hch (hvnj (j + 1) S ρ)
      | 1, hch => exact ⟨c, Or.inl hch⟩
      | 2, hch =>
        have e : Fw (app (app S S) ρ) c 2 = app (app (app S S) ρ) (app c (app (app S S) ρ)) := rfl
        rw [e] at hch
        obtain ⟨k, _, hk, h2⟩ := gamma_walk v hv hvnj (j + 1) (app S S) ρ _ hch hρ (hcZ c)
        have := tw_eq_one k hk
        subst this
        exact ⟨c, Or.inr h2⟩
      | 3, hch =>
        exfalso
        have e : Fw (app (app S S) ρ) c 3 =
            app (app c (app (app S S) ρ)) (app (app (app S S) ρ) (app c (app (app S S) ρ))) := rfl
        rw [e] at hch
        have hσ : ¬ Tower (app (app (app S S) ρ) (app c (app (app S S) ρ))) := app_nontower _ _ (hcZ c)
        obtain ⟨k, hk2, hk, h2⟩ := gamma_walk v hv hvnj (j + 1) c _ _ hch hZnt hσ
        match k, hk2, hk, h2 with
        | 0, _, hk, h2 =>
          have e0 : Fw (app (app (app S S) ρ) (app c (app (app S S) ρ))) (app (app S S) ρ) 0 =
              app (app (app S S) ρ) (app c (app (app S S) ρ)) := rfl
          rw [e0] at h2
          obtain ⟨k', _, hk', h3⟩ := gamma_walk v hv hvnj (j + 1 + 1) (app S S) ρ _ h2 hρ (hcZ c)
          have := tw_eq_one k' hk'
          subst this
          have e1 : Fw (app c (app (app S S) ρ)) ρ 0 = app c (app (app S S) ρ) := rfl
          rw [e1, hk] at h3
          exact hvnj (j + 1 + 1 + 1) S _ h3
        | 1, _, hk, h2 =>
          have e0 : Fw (app (app (app S S) ρ) (app c (app (app S S) ρ))) (app (app S S) ρ) 1 =
              app (app (app S S) ρ) (app (app (app S S) ρ) (app c (app (app S S) ρ))) := rfl
          rw [e0] at h2
          obtain ⟨k', _, hk', h3⟩ := gamma_walk v hv hvnj (j + 1 + 1) (app S S) ρ _ h2 hρ hσ
          have := tw_eq_one k' hk'
          subst this
          have e1 : Fw (app (app (app S S) ρ) (app c (app (app S S) ρ))) ρ 0 =
              app (app (app S S) ρ) (app c (app (app S S) ρ)) := rfl
          rw [e1] at h3
          obtain ⟨k'', _, hk'', h4⟩ := gamma_walk v hv hvnj (j + 1 + 1 + 1) (app S S) ρ _ h3 hρ (hcZ c)
          have := tw_eq_one k'' hk''
          subst this
          have e2 : Fw (app c (app (app S S) ρ)) ρ 0 = app c (app (app S S) ρ) := rfl
          rw [e2, hk] at h4
          exact hvnj (j + 1 + 1 + 1 + 1) (tw 1) _ h4
        | 2, _, _, h2 =>
          have e0 : Fw (app (app (app S S) ρ) (app c (app (app S S) ρ))) (app (app S S) ρ) 2 =
              app (app (app (app S S) ρ) (app c (app (app S S) ρ)))
                (app (app (app S S) ρ) (app (app (app S S) ρ) (app c (app (app S S) ρ)))) := rfl
          rw [e0] at h2
          obtain ⟨k', _, hk', _⟩ := gamma_walk v hv hvnj (j + 1 + 1) (app (app S S) ρ) _ _ h2 (hcZ c)
            (app_nontower _ _ hσ)
          exact hZnt ⟨k' + 1, hk'⟩
      | m + 4, hch =>
        exfalso
        have hnt : ∀ i, ¬ Tower (Fw (app (app S S) ρ) c i) := fun i => SA3.fw_nontower _ c hZnt i
        have e : Fw (app (app S S) ρ) c (m + 4) =
            app (app (Fw (app (app S S) ρ) c m) (Fw (app (app S S) ρ) c (m + 1)))
              (Fw (app (app S S) ρ) c (m + 3)) := by
          rw [show m + 4 = (m + 2) + 2 by omega, Fw_add2, Fw_add2]
        rw [e] at hch
        obtain ⟨k', _, hk', _⟩ := gamma_walk v hv hvnj (j + 1) _ _ _ hch (hnt (m + 1)) (hnt (m + 3))
        exact hnt m ⟨k' + 1, hk'⟩
  have hret : ∀ N, ∃ j, N ≤ j ∧ ∃ q, v j = app q (app (app S S) ρ) := by
    have hgo : ∀ N, ∃ j, N ≤ j ∧ ∃ q, v j = app q (app (app S S) ρ) := by
      intro N
      induction N with
      | zero => exact ⟨0, Nat.le_refl _, X, by show u (t + 0) = _; rw [Nat.add_zero]; exact hu⟩
      | succ N ih =>
        obtain ⟨j, hj, q, hq⟩ := ih
        obtain ⟨X'', h⟩ := hnext j q hq
        rcases h with h | h
        · exact ⟨j + 1, by omega, X'', h⟩
        · exact ⟨j + 2, by omega, X'', h⟩
    exact hgo
  exact SA.no_scenarioA v hv _ hZnt hvnj habove hret

end DP

#print axioms DP.no_SS_letter

namespace DP

open C
open C.T
open FM

/-- the word of n letters S(SS) on top of Y -/
def Twr2 (Y : T) : Nat → T
  | 0 => Y
  | n + 1 => app (tw 2) (Twr2 Y n)

theorem Twr2_suf (Y : T) : ∀ n, Suf Y (Twr2 Y n)
  | 0 => Suf.refl
  | n + 1 => Suf.wrap _ _ (Twr2_suf Y n)

theorem Twr2_nontower (Y : T) (hY : ¬ Tower Y) (n : Nat) : ¬ Tower (Twr2 Y n) :=
  suf_nontower Y _ (Twr2_suf Y n) hY

/-- **S(SS) letters are skipped.**  A node (S(SS)^n Y).X with Y, X non-towers reaches Y.X in n steps. -/
theorem tw2_skips (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (Y X : T) (hY : ¬ Tower Y) (hX : ¬ Tower X) :
    ∀ n t, u t = app (Twr2 Y n) X → u (t + n) = app Y X := by
  intro n
  induction n with
  | zero => intro t h; exact h
  | succ n ih =>
    intro t h
    have h' : u t = app (app (tw 2) (Twr2 Y n)) X := h
    obtain ⟨k, _, hk, h1⟩ := gamma_walk u hchild hnj t (tw 2) (Twr2 Y n) X h' (Twr2_nontower Y hY n) hX
    have := SA3.tw_inj 2 (k + 1) hk
    obtain rfl : k = 1 := by omega
    have e : Fw X (Twr2 Y n) 1 = app (Twr2 Y n) X := rfl
    rw [e] at h1
    have := ih (t + 1) h1
    rwa [show t + 1 + n = t + (n + 1) by omega] at this

/-- **No Omega-type push over a stack S(SS)^n (S(S(SS)) B).**  In a jump-free infinite leftmost walk, no computed step
    with H(q) = S (S(SS)) c (a K = 2 push) starts from a node q.σ whose stack σ is a word of S(SS) letters on top of a
    letter S(S(SS)) with a non-tower rest B.  (The copy σ put on top is read: the S(SS) letters are skipped, the
    S(S(SS)) letter pushes B and puts the current stack c.σ on top; reading c.σ meets c (SS is excluded by
    no_SS_letter), then the same S(SS)-letters and S(S(SS)) letter again, and finally the non-tower letter B, which the
    reading lemma forbids.)  So every copy put on top by a K = 2 step is read through S(SS)-letters and never meets an
    S(S(SS)) letter before its first other letter. -/
theorem no_tw3_push (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (t : Nat) (q c B : T) (n : Nat) (hB : ¬ Tower B)
    (hu : u t = app q (Twr2 (app (tw 3) B) n)) (hq : 2 ≤ (args q).length)
    (hK : Reach (args q) [tw 2, c]) : False := by
  have h3B : ¬ Tower (app (tw 3) B) := app_nontower _ _ hB
  have hσ : ¬ Tower (Twr2 (app (tw 3) B) n) := Twr2_nontower _ h3B n
  -- the K = 2 step
  have hc := hchild t
  rw [hu] at hc
  rcases hc with ⟨hlen, _, _⟩ | ⟨_, dd, hrr⟩
  · exfalso; rw [args_app] at hlen; simp at hlen; omega
  obtain ⟨K, c', hK', hch⟩ := fib_step q _ _ dd hq hσ hrr
  have e := RC.reach_det _ _ _ hK hK' (by simp) (by simp)
  simp only [List.cons.injEq] at e
  obtain ⟨hKK, hcc, _⟩ := e
  have hK2 : K = 2 := (SA3.tw_inj 2 K hKK).symm
  subst hK2; subst hcc
  -- u (t+1) = σ.(c.σ)
  have h1 : u (t + 1) = app (Twr2 (app (tw 3) B) n) (app c (Twr2 (app (tw 3) B) n)) := hch
  have hcσ : ¬ Tower (app c (Twr2 (app (tw 3) B) n)) := app_nontower _ _ hσ
  -- skip the S(SS) letters, then read S(S(SS))
  have h2 := tw2_skips u hchild hnj (app (tw 3) B) _ h3B hcσ n (t + 1) h1
  obtain ⟨k, _, hk, h3⟩ := gamma_walk u hchild hnj (t + 1 + n) (tw 3) B _ h2 hB hcσ
  have := SA3.tw_inj 3 (k + 1) hk
  obtain rfl : k = 2 := by omega
  have e2 : Fw (app c (Twr2 (app (tw 3) B) n)) B 2 =
      app (app c (Twr2 (app (tw 3) B) n)) (app B (app c (Twr2 (app (tw 3) B) n))) := rfl
  rw [e2] at h3
  have hBc : ¬ Tower (app B (app c (Twr2 (app (tw 3) B) n))) := app_nontower _ _ hcσ
  obtain ⟨k', hk'2, hk', h4⟩ := gamma_walk u hchild hnj (t + 1 + n + 1) c _ _ h3 hσ hBc
  match k', hk'2, hk', h4 with
  | 0, _, hk', _ =>
    -- c = SS: the node u (t+1) = σ.(SS.σ) is excluded by no_SS_letter
    exact no_SS_letter u hchild hnj (t + 1) _ _ hσ (by rw [h1, hk']; rfl)
  | 1, _, _, h4 =>
    have e3 : Fw (app B (app c (Twr2 (app (tw 3) B) n))) (Twr2 (app (tw 3) B) n) 1 =
        app (Twr2 (app (tw 3) B) n) (app B (app c (Twr2 (app (tw 3) B) n))) := rfl
    rw [e3] at h4
    have h5 := tw2_skips u hchild hnj (app (tw 3) B) _ h3B hBc n _ h4
    obtain ⟨k2, _, hk2, h6⟩ := gamma_walk u hchild hnj _ (tw 3) B _ h5 hB hBc
    have := SA3.tw_inj 3 (k2 + 1) hk2
    obtain rfl : k2 = 2 := by omega
    have e4 : Fw (app B (app c (Twr2 (app (tw 3) B) n))) B 2 =
        app (app B (app c (Twr2 (app (tw 3) B) n))) (app B (app B (app c (Twr2 (app (tw 3) B) n)))) := rfl
    rw [e4] at h6
    obtain ⟨k3, _, hk3, _⟩ := gamma_walk u hchild hnj _ B _ _ h6 hcσ (app_nontower _ _ hBc)
    exact hB ⟨k3 + 1, hk3⟩
  | 2, _, _, h4 =>
    have e3 : Fw (app B (app c (Twr2 (app (tw 3) B) n))) (Twr2 (app (tw 3) B) n) 2 =
        app (app B (app c (Twr2 (app (tw 3) B) n)))
          (app (Twr2 (app (tw 3) B) n) (app B (app c (Twr2 (app (tw 3) B) n)))) := rfl
    rw [e3] at h4
    obtain ⟨k3, _, hk3, _⟩ := gamma_walk u hchild hnj _ B _ _ h4 hcσ (app_nontower _ _ hBc)
    exact hB ⟨k3 + 1, hk3⟩

end DP

#print axioms DP.tw2_skips
#print axioms DP.no_tw3_push
