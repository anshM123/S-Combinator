
/-! ### Theorem PBT: pattern beta with c0 = S.a1 needs no hypothesis beyond its own glue (H1ok is automatic) -/

/-- h1 occurs only inside copies of h1.h2 -/
def gH (h1 h2 : Nat) : T → Prop
  | S => True
  | var n => n ≠ h1
  | app f x => (f = var h1 ∧ x = var h2) ∨ (gH h1 h2 f ∧ gH h1 h2 x)

theorem gH_headS_args (h1 h2 : Nat) : ∀ t : T, gH h1 h2 t → head t = S → ∀ s ∈ args t, gH h1 h2 s
  | S, _, _, s, hs => by simp [args] at hs
  | var _, _, hh, _, _ => by simp [head] at hh
  | app f x, h, hh, s, hs => by
    rcases h with ⟨hf, _⟩ | ⟨hf, hx⟩
    · subst hf; simp [head] at hh
    · simp [args] at hs
      rcases hs with hs | hs
      · exact gH_headS_args h1 h2 f hf (by simpa [head] using hh) s hs
      · subst hs; exact hx

theorem gH_h1head (h1 h2 : Nat) : ∀ t : T, gH h1 h2 t → head t = var h1 → (args t).head? = some (var h2)
  | S, _, hh => by simp [head] at hh
  | var n, h, hh => by simp [head] at hh; subst hh; simp [gH] at h
  | app f x, h, hh => by
    rcases h with ⟨hf, hx⟩ | ⟨hf, _⟩
    · subst hf; subst hx; simp [args]
    · have := gH_h1head h1 h2 f hf (by simpa [head] using hh)
      simp only [args]
      cases hfa : args f with
      | nil => rw [hfa] at this; simp at this
      | cons u us => rw [hfa] at this; simpa using this

theorem gH_run (h1 h2 : Nat) : ∀ (k : Nat) (L L' : List T), (∀ e ∈ L, gH h1 h2 e) → run k L = some L' →
    ∀ e ∈ L', gH h1 h2 e
  | 0, L, L', h0, h => by simp [run] at h; subst h; exact h0
  | k + 1, L, L', h0, h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      simp only at h
      apply gH_run h1 h2 k L1 L' _ h
      match L, hs, h0 with
      | a :: b :: d :: R, hs, h0 =>
        simp only [step] at hs
        split at hs
        · rename_i haS
          injection hs with hs; subst hs
          intro e he; simp at he
          rcases he with he | he | he | he
          · exact gH_headS_args h1 h2 a (h0 a (by simp)) haS e he
          · rw [he]; exact h0 d (by simp)
          · rw [he]; exact Or.inr ⟨h0 b (by simp), h0 d (by simp)⟩
          · exact h0 e (by simp [he])
        · simp at hs
      | [], hs, _ => simp [step] at hs
      | [_], hs, _ => simp [step] at hs
      | [_, _], hs, _ => simp [step] at hs

theorem gH_free (h1 h2 : Nat) : ∀ t : T, occN h1 t = 0 → gH h1 h2 t
  | S, _ => trivial
  | var n, h => by
    show n ≠ h1
    intro e; subst e; simp [occN] at h
  | app f x, h => by
    simp only [occN] at h
    exact Or.inr ⟨gH_free h1 h2 f (by omega), gH_free h1 h2 x (by omega)⟩

/-- H1ok holds automatically for c0 = S.a1 -/
theorem h1ok_Sa1 (a1 : T) (h1 h2 : Nat) (h12 : h1 ≠ h2) (ha1S : head a1 = S) (hf1 : occN h1 a1 = 0) :
    ∀ (k : Nat) (g : T) (L : List T), run k (args (app S a1) ++ [var h1, var h2]) = some (g :: L) →
      head g = var h1 → (args g).head? = some (var h2) ∨ (args g = [] ∧ ∃ b' R', L = b' :: var h2 :: R') := by
  intro k g L hk hg
  left
  match k, hk with
  | 0, hk =>
    simp [args, run] at hk
    rw [← hk.1, ha1S] at hg; simp at hg
  | k' + 1, hk =>
    have hs : step (args (app S a1) ++ [var h1, var h2]) = some (args a1 ++ [var h2, app (var h1) (var h2)]) := by
      simp [args, step, ha1S]
    simp only [run] at hk
    rw [hs] at hk
    simp only at hk
    have h0 : ∀ e ∈ args a1 ++ [var h2, app (var h1) (var h2)], gH h1 h2 e := by
      intro e he; simp at he
      rcases he with he | he | he
      · exact gH_free h1 h2 e (occN_args h1 a1 hf1 e he)
      · rw [he]; show h2 ≠ h1; exact Ne.symm h12
      · rw [he]; exact Or.inl ⟨rfl, rfl⟩
    have hgg := gH_run h1 h2 k' _ _ h0 hk g (by simp)
    exact gH_h1head h1 h2 g hgg hg

/-- **THEOREM PBT (pattern beta with c0 = S.a1, no replay hypothesis).**  If the earlier phase (any run from L0)
    opens the element (S.a1).w with y at position 3 - i.e. reaches [(S.a1).w, b, y] ++ R0, where w = b0.(S.a1) -
    and later reaches a p-front list with >= 3 elements, then the next phase of w.y never makes a proper transfer. -/
theorem pbt_main (b0 a1 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H) (hb0S : head b0 = S) (ha1S : head a1 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 a1 = 0)
    (hf1 : occN h1 a1 = 0) (hf2 : occN h2 a1 = 0) (hV : fresh3 H (app (app b0 (app S a1)) (var 2)))
    (L0 : List T) (t T' : Nat) (b0' : T) (R0 : List T)
    (hfront : run t L0 = some (app (app S a1) (app b0 (app S a1)) :: b0' :: var 2 :: R0))
    (htT : t < T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c (app S a1))) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  have hc0S : head (app S a1) = S := by simp [head]
  have hy1' : occ2 (app S a1) = 0 := by simp [occ2]; exact hy1
  have hf1' : occN h1 (app S a1) = 0 := by simp [occN]; exact hf1
  have hf2' : occN h2 (app S a1) = 0 := by simp [occN]; exact hf2
  -- one step after the beta1 front: c0 runs on (w, y)
  have hc0w : run (t + 1) L0 = some (args (app S a1) ++ app b0 (app S a1) :: var 2 :: app b0' (var 2) :: R0) := by
    rw [run_add t 1, hfront, Option.bind_some]
    simp [run, step, head, args]
  have hT1 : t + 1 < T' ∨ t + 1 = T' := by omega
  rcases hT1 with hlt | heq
  · exact beta_main b0 (app S a1) c h1 h2 H hc hc2 hh1 hh2 h12 hH hb0S hc0S hy0 hy1' hf1' hf2' hV L0 (t + 1) T'
      (app b0' (var 2) :: R0) hc0w hlt f b d R hT hf (h1ok_Sa1 a1 h1 h2 h12 ha1S hf1)
  · exfalso
    subst heq
    rw [hc0w] at hT
    simp [args] at hT
    rw [← hT.1, ha1S] at hf; simp at hf
