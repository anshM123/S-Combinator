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

