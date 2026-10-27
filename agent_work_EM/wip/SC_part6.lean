
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
