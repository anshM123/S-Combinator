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

/-! ## Strict cuts in deep walks — SC (agent_work_EM, 2026-10-27) -/

namespace SC

open C
open C.T
open FM
open DP

/-- the Fibonacci child is determined by H(b) -/
theorem fib_next (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (s : Nat) (b X c : T) (K : Nat) (hX : ¬ Tower X) (hb : 2 ≤ (args b).length)
    (hs : u s = app b X) (hK : Reach (args b) [tw K, c]) : u (s + 1) = Fw X c K := by
  have hc := hchild s
  rw [hs] at hc
  rcases hc with ⟨hlen, _, _⟩ | ⟨_, dd, hrr⟩
  · exfalso; rw [args_app] at hlen; simp at hlen; omega
  obtain ⟨K', c', hK', hch⟩ := fib_step b X _ dd hb hX hrr
  have e := RC.reach_det _ _ _ hK hK' (by simp) (by simp)
  simp only [List.cons.injEq] at e
  obtain ⟨h1, h2, _⟩ := e
  have := SA3.tw_inj K K' h1
  subst this; subst h2
  exact hch

/-- every term is S(SS)^n Y with Y not headed by the letter S(SS) -/
theorem twr2_decomp : ∀ σ : T, ∃ n Y, σ = Twr2 Y n ∧ ∀ Y', Y ≠ app (tw 2) Y'
  | S => ⟨0, S, rfl, fun Y' h => by cases h⟩
  | app f x => by
    by_cases hf : f = tw 2
    · obtain ⟨n, Y, hx, hY⟩ := twr2_decomp x
      exact ⟨n + 1, Y, by rw [hf, hx]; rfl, hY⟩
    · exact ⟨0, app f x, rfl, fun Y' h => by
        simp only [app.injEq] at h; exact hf h.1⟩

/-- the base program: tail calls b 0 = Y, ..., b i0, then a step with K0 /= 1 -/
def BaseChain (Y : T) (i0 : Nat) (b : Nat → T) (K0 : Nat) (c0 : T) : Prop :=
  b 0 = Y ∧ (∀ i, i < i0 → 2 ≤ (args (b i)).length ∧ Reach (args (b i)) [tw 1, b (i + 1)]) ∧
  2 ≤ (args (b i0)).length ∧ Reach (args (b i0)) [tw K0, c0] ∧ K0 ≠ 1

/-- running the base program over any non-tower stack -/
theorem base_run (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (Y : T) (i0 : Nat) (b : Nat → T) (K0 : Nat) (c0 : T) (hBC : BaseChain Y i0 b K0 c0)
    (X : T) (hX : ¬ Tower X) (s : Nat) (hs : u s = app Y X) :
    (∀ i, i ≤ i0 → u (s + i) = app (b i) X) ∧ u (s + i0 + 1) = Fw X c0 K0 := by
  obtain ⟨hb0, htail, hlast2, hlast, _⟩ := hBC
  have hrun : ∀ i, i ≤ i0 → u (s + i) = app (b i) X := by
    intro i
    induction i with
    | zero => intro _; rw [hb0]; exact hs
    | succ i ih =>
      intro hi
      obtain ⟨h2, hr⟩ := htail i (by omega)
      have := fib_next u hchild (s + i) (b i) X (b (i + 1)) 1 hX h2 (ih (by omega)) hr
      rw [show s + (i + 1) = s + i + 1 by omega]
      exact this
  exact ⟨hrun, fib_next u hchild (s + i0) (b i0) X c0 K0 hX hlast2 (hrun i0 (Nat.le_refl _)) hlast⟩

/-- the base program exists when the walk never comes back to the stack X -/
theorem base_exists (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ) (s : Nat) (Y X : T) (hX : ¬ Tower X)
    (hs : u s = app Y X) (hnoX : ∀ e, u (s + e) ≠ X) :
    ∃ i0 b K0 c0, BaseChain Y i0 b K0 c0 := by
  let b : Nat → T := fun i => lchild (u (s + i))
  -- one step from a node (b i).X
  have hone : ∀ i, u (s + i) = app (b i) X → 2 ≤ (args (b i)).length ∧ ∃ K c,
      Reach (args (b i)) [tw K, c] ∧ u (s + i + 1) = Fw X c K ∧ K ≠ 0 := by
    intro i hi
    have hc := hchild (s + i)
    rw [hi] at hc
    rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, dd, hrr⟩
    · exfalso
      rw [args_app] at hlen hrr
      match hq : args (b i), hlen, hrr with
      | [], _, hrr =>
        simp only [List.nil_append, List.cons.injEq] at hrr
        exact hnoX (i + 1) (by rw [show s + (i + 1) = s + i + 1 by omega]; exact hrr.1.symm)
      | [p], _, _ => exact hnj (s + i) p X (by rw [hi, TC.args_one' (b i) p hq])
      | _ :: _ :: _, hlen, _ => simp at hlen
    · rw [args_app] at hlen
      have h2 : 2 ≤ (args (b i)).length := by simp at hlen; omega
      obtain ⟨K, c, hK, hch⟩ := fib_step (b i) X _ dd h2 hX hrr
      refine ⟨h2, K, c, hK, hch, fun h0 => ?_⟩
      subst h0
      exact hnoX (i + 1) (by rw [show s + (i + 1) = s + i + 1 by omega]; exact hch)
  have hb0 : u (s + 0) = app (b 0) X := by
    show u (s + 0) = app (lchild (u (s + 0))) X
    rw [Nat.add_zero, hs]; rfl
  -- either some step has K /= 1, or all are tail calls (an infinite R2-chain)
  refine Classical.byContradiction (fun hno => ?_)
  have hall : ∀ i, u (s + i) = app (b i) X ∧ Reach (args (b i)) [tw 1, b (i + 1)] := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
      have hi : u (s + i) = app (b i) X := by
        cases i with
        | zero => exact hb0
        | succ i' =>
          have h := (ih i' (by omega)).1
          obtain ⟨_, K, c, hK, hch, _⟩ := hone i' h
          have hK1 := (ih i' (by omega)).2
          have e := RC.reach_det _ _ _ hK hK1 (by simp) (by simp)
          simp only [List.cons.injEq] at e
          obtain ⟨e1, e2, _⟩ := e
          have := SA3.tw_inj K 1 e1
          subst this; subst e2
          have hn : u (s + (i' + 1)) = app (b (i' + 1)) X := by
            rw [show s + (i' + 1) = s + i' + 1 by omega]; exact hch
          exact hn
      refine ⟨hi, ?_⟩
      obtain ⟨h2, K, c, hK, hch, hK0⟩ := hone i hi
      by_cases hK1 : K = 1
      · subst hK1
        have hc' : c = b (i + 1) := by
          show c = lchild (u (s + (i + 1)))
          rw [show s + (i + 1) = s + i + 1 by omega, hch]; rfl
        rw [← hc']; exact hK
      · exfalso
        apply hno
        refine ⟨i, b, K, c, (by show lchild (u (s + 0)) = Y; rw [Nat.add_zero, hs]; rfl),
          fun i' hi' => ?_, h2, hK, hK1⟩
        have hp := (ih i' hi').2
        refine ⟨(hone i' (ih i' hi').1).1, hp⟩
  exact no_R2_chain b (fun i => (hall i).2)

end SC

#print axioms SC.fib_next
#print axioms SC.twr2_decomp
#print axioms SC.base_run
#print axioms SC.base_exists

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

namespace SC

open C
open C.T
open FM
open DP

/-- **Strict cuts on tower stacks: the S-push dichotomy.**  In a jump-free infinite leftmost walk whose depth tends to
    infinity, let t be a strict cut whose stack is a tower tw m.  Then either a later strict cut sits on a non-tower
    stack (so SC.EM_of_cut applies), or the node at t is (S x S).(tw m) and its child pushes the letter S directly
    on the tower (the child has tw (m+1) as a right-spine suffix).  The letter pushed directly above the old stack is
    always the second component c0 of H(q) (SA3.wh_c0); if c0 /= S the segment c0.(tw m) is a frozen non-tower. -/
theorem tower_cut_S (u : Nat → C.T) (hchild : ∀ j, FH.LChild (u j) (u (j + 1)))
    (hnj : ∀ j p τ, u j ≠ app (app S p) τ)
    (hdeep : ∀ d, ∃ N, ∀ j, N ≤ j → d < SA2.msl (u j))
    (t m : Nat) (q : T) (hu : u t = app q (tw m))
    (hcut : ∀ e, SA2.msl (u t) < SA2.msl (u (t + 1 + e))) :
    (∃ t', t < t' ∧ ¬ Tower (SA.rpart (u t')) ∧ ∀ e, SA2.msl (u t') < SA2.msl (u (t' + 1 + e))) ∨
    (∃ x, q = app (app S x) S ∧ Suf (tw (m + 1)) (u (t + 1))) := by
  have hmsl_t : SA2.msl (u t) = m + 1 := by
    rw [hu]; simp only [SA2.msl]
    have : ∀ k, SA2.msl (tw k) = k := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => simp only [tw, SA2.msl, ih]
    rw [this]
  have hc := hchild t
  rw [hu] at hc
  rcases hc with ⟨hlen, rest, hrr⟩ | ⟨hlen, dd, hrr⟩
  · exfalso
    rw [args_app] at hlen hrr
    match hq : args q, hlen, hrr with
    | [], _, hrr =>
      simp only [List.nil_append, List.cons.injEq] at hrr
      have h0 := hcut 0
      rw [Nat.add_zero, ← hrr.1, hmsl_t] at h0
      have : ∀ k, SA2.msl (tw k) = k := by
        intro k; induction k with
        | zero => rfl
        | succ k ih => simp only [tw, SA2.msl, ih]
      rw [this] at h0
      omega
    | [p], _, _ => exact hnj t p (tw m) (by rw [hu, TC.args_one' q p hq])
    | _ :: _ :: _, hlen, _ => simp at hlen
  · rw [args_app] at hlen
    have hq2 : 2 ≤ (args q).length := by simp at hlen; omega
    have hrr' : Reach (args q ++ [tw m]) [u (t + 1), dd] := by rw [← args_app]; exact hrr
    have hmsl_c : m + 2 ≤ SA2.msl (u (t + 1)) := by have := hcut 0; rw [Nat.add_zero, hmsl_t] at this; omega
    -- the letter directly above tw m in the child is the second component c0 of H(q)
    obtain ⟨x0, c0, hq0, hsuf⟩ : ∃ x0 c0, Reach (args q) [x0, c0] ∧ Suf (app c0 (tw m)) (u (t + 1)) := by
      rcases OM.cinv2_reach q (tw m) hq2 _ hrr' with ⟨L1, _, hlen1, hEq⟩ | ⟨x, c1, w', P, _, _, _, hlen1, hEq⟩ |
          ⟨x, c', w', b, _, hH, _, hEq⟩ | ⟨y, _, hEq⟩
      · have := congrArg List.length hEq; simp at this; omega
      · have := congrArg List.length hEq; simp at this; omega
      · simp only [List.cons.injEq] at hEq
        obtain ⟨hc', _, _⟩ := hEq
        obtain ⟨x0, c0, hq0, hcase⟩ := SA3.wh_c0 q (tw m) x c' w' hH
        refine ⟨x0, c0, hq0, ?_⟩
        rw [hc']
        rcases hcase with ⟨hw, hcc⟩ | hs
        · rw [hw, hcc]; exact Suf.refl
        · exact Suf.wrap _ _ hs
      · simp only [List.cons.injEq] at hEq
        exfalso
        have h1 := hEq.1
        rw [h1] at hmsl_c
        have : ∀ k, SA2.msl (tw k) = k := by
          intro k; induction k with
          | zero => rfl
          | succ k ih => simp only [tw, SA2.msl, ih]
        rw [this] at hmsl_c
        omega
    have htwm : ∀ k, SA2.msl (tw k) = k := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => simp only [tw, SA2.msl, ih]
    -- the segment c0.(tw m) is frozen from t+1 on
    have hfrozen : ∀ e, Suf (app c0 (tw m)) (u (t + 1 + e)) ∧ u (t + 1 + e) ≠ app c0 (tw m) := by
      intro e
      induction e with
      | zero =>
        refine ⟨by simpa using hsuf, fun h => ?_⟩
        have := hcut 0
        rw [Nat.add_zero, h, hmsl_t] at this
        simp only [SA2.msl, htwm] at this
        omega
      | succ e ih =>
        refine ⟨?_, fun h => ?_⟩
        · rw [show t + 1 + (e + 1) = t + 1 + e + 1 by omega]
          exact SA.step_keeps _ _ _ (hchild (t + 1 + e)) ih.1 ih.2 (hnj (t + 1 + e))
        · have := hcut (e + 1)
          rw [h, hmsl_t] at this
          simp only [SA2.msl, htwm] at this
          omega
    by_cases hc0 : c0 = S
    · -- the S-push case
      subst hc0
      right
      by_cases h3 : 3 ≤ (args q).length
      · exfalso
        obtain ⟨b, hb⟩ := final_app _ _ _ h3 hq0
        cases hb
      · have e := reach_stuck _ _ (by omega) hq0
        refine ⟨x0, RC.args_two q x0 S e.symm, ?_⟩
        exact hsuf
    · -- a frozen non-tower letter: every later strict cut sits on a non-tower stack
      left
      have hFnt : ¬ Tower (app c0 (tw m)) := by
        rintro ⟨k, hk⟩
        cases k with
        | zero => cases hk
        | succ k =>
          simp only [tw, app.injEq] at hk
          exact hc0 hk.1
      obtain ⟨N, hN⟩ := hdeep (SA2.msl (u (t + 1)))
      obtain ⟨t', ht'1, ht'd, ht'cut⟩ := last_le (fun j => SA2.msl (u j)) (SA2.msl (u (t + 1))) (t + 1)
        (Nat.le_refl _) (t + 1 + N + 1) (by omega) (fun j hj => hN j (by omega))
      have hd' : SA2.msl (u t') ≤ SA2.msl (u (t + 1)) := ht'd
      refine ⟨t', by omega, ?_, fun e => by
        have h : SA2.msl (u (t + 1)) < SA2.msl (u (t' + 1 + e)) := ht'cut e
        omega⟩
      obtain ⟨hs', hne'⟩ := hfrozen (t' - (t + 1))
      rw [show t + 1 + (t' - (t + 1)) = t' by omega] at hs' hne'
      match hut' : u t' with
      | S => rw [hut'] at hs'; exact absurd (suf_S _ hs') (by intro h; cases h)
      | app a b =>
        rw [hut'] at hs' hne'
        simp only [SA.rpart]
        rcases suf_app_inv _ a b hs' with h | h
        · exact absurd h hne'
        · exact suf_nontower _ _ h hFnt

end SC

#print axioms SC.tower_cut_S

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
