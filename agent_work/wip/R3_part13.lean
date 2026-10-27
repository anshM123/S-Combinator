
/-- generic first-barrier lemma with an arbitrary invariant preserved by non-barrier S-headed steps -/
theorem phaseQ (bar : T → Bool) (Inv : List T → Prop)
    (hInv : ∀ f b d R, Inv (f :: b :: d :: R) → bar f = false → head f = S → Inv (args f ++ d :: app b d :: R))
    (L0 : List T) (h0 : Inv L0) :
    ∀ (m : Nat) (L : List T), run m L0 = some L →
    Inv L ∨ ∃ m1 L1, m1 < m ∧ run m1 L0 = some L1 ∧ Inv L1 ∧
      (∃ f b d R, L1 = f :: b :: d :: R ∧ bar f = true) ∧ run (m - m1) L1 = some L
  | 0, L, h => by simp [run] at h; subst h; exact Or.inl h0
  | m + 1, L, h => by
    have hadd := run_add m 1 L0
    rw [h] at hadd
    cases hm : run m L0 with
    | none => rw [hm] at hadd; simp at hadd
    | some Lm =>
      rw [hm] at hadd
      have h1 : run 1 Lm = some L := by simpa using hadd.symm
      have hstep : step Lm = some L := by
        simp only [run] at h1
        cases hs : step Lm with
        | none => rw [hs] at h1; simp at h1
        | some L' => rw [hs] at h1; simp at h1; rw [h1]
      rcases phaseQ bar Inv hInv L0 h0 m Lm hm with hB | ⟨m1, L1, hlt, hr1, hb1, hx1, hrest⟩
      · match Lm, hB, hstep, hm with
        | f :: b :: d :: R, hB, hstep, hm =>
          by_cases hb : bar f = true
          · right
            exact ⟨m, f :: b :: d :: R, by omega, hm, hB, ⟨f, b, d, R, rfl, hb⟩, by simpa using h1⟩
          · left
            simp only [step] at hstep
            split at hstep
            · rename_i hfS
              injection hstep with hstep; subst hstep
              exact hInv f b d R hB (by simpa using hb) hfS
            · simp at hstep
        | [], _, hstep, _ => simp [step] at hstep
        | [_], _, hstep, _ => simp [step] at hstep
        | [_, _], _, hstep, _ => simp [step] at hstep
      · right
        refine ⟨m1, L1, by omega, hr1, hb1, hx1, ?_⟩
        have hadd2 := run_add (m - m1) 1 L1
        rw [hrest] at hadd2
        rw [show m + 1 - m1 = (m - m1) + 1 by omega, hadd2]
        simpa using h1

def rcombT : List T → T → T
  | [], t => t
  | d :: ds, t => app d (rcombT ds t)

def NHc (c0 : T) (h1 h2 : Nat) : Prop := ∀ (k : Nat) (g : T) (L : List T),
  run k (args c0 ++ [var h1, var h2]) = some (g :: L) → head g ≠ var h1 ∧ head g ≠ var h2

/-- a phase-2 wrapper satisfying the hypotheses of PAF -/
def WOK (h1 h2 : Nat) (u : T) : Prop := ∃ b0 c0, u = app b0 c0 ∧ head b0 = S ∧ head c0 = S ∧ occ2 b0 = 0 ∧
  occ2 c0 = 0 ∧ occN h1 c0 = 0 ∧ occN h2 c0 = 0 ∧ NHc c0 h1 h2

theorem guarded_free (Lv : T) : ∀ t : T, occN 0 t = 0 → guarded Lv t
  | S, _ => trivial
  | var n, h => by
    show n ≠ 0
    intro e; subst e; simp [occN] at h
  | app f x, h => by
    simp only [occN] at h
    exact Or.inr ⟨guarded_free Lv f (by omega), guarded_free Lv x (by omega)⟩

theorem sb_free0 (c : Nat) (hc : c ≠ 0) : ∀ t : T, occN 0 (sb c t) = 0
  | S => by simp [sb, occN]
  | var n => by
    by_cases h0 : n = 0
    · subst h0; simp [sb, occN, hc]
    · simp [sb, occN, h0]
  | app f x => by simp [sb, occN, sb_free0 c hc f, sb_free0 c hc x]

theorem guarded_mono (u Lv2 : T) (hu : occN 0 u = 0) (hL2 : ∃ f x, Lv2 = app f x) :
    ∀ t : T, guarded (app u Lv2) t → guarded Lv2 t
  | S, _ => trivial
  | var n, h => h
  | app f x, h => by
    rcases h with h | ⟨hf, hx⟩
    · rw [h]
      refine Or.inr ⟨guarded_free Lv2 u hu, ?_⟩
      obtain ⟨g, z, hgz⟩ := hL2
      rw [hgz]; exact Or.inl rfl
    · exact Or.inr ⟨guarded_mono u Lv2 hu hL2 f hf, guarded_mono u Lv2 hu hL2 x hx⟩

theorem guarded_prefix_args (Lv : T) : ∀ f : T, wpre Lv f → guarded Lv f →
    ∃ us, args f = args Lv ++ us ∧ ∀ u ∈ us, guarded Lv u
  | S, h, _ => by simp [wpre] at h; subst h; exact ⟨[], by simp, by simp⟩
  | var n, h, _ => by simp [wpre] at h; subst h; exact ⟨[], by simp, by simp⟩
  | app g x, h, hg => by
    by_cases he : app g x = Lv
    · rw [he]; exact ⟨[], by simp, by simp⟩
    · have hwg : wpre Lv g := by
        rcases h with h | h
        · exact absurd h he
        · exact h
      rcases hg with hg | ⟨hgg, hgx⟩
      · exact absurd hg he
      · obtain ⟨us, hus, hall⟩ := guarded_prefix_args Lv g hwg hgg
        refine ⟨us ++ [x], by simp [args, hus], ?_⟩
        intro u hu; simp at hu
        rcases hu with hu | hu
        · exact hall u hu
        · subst hu; exact hgx

theorem occ2_rcombT (c : Nat) (hc2 : c ≠ 2) : ∀ (us : List T), (∀ u ∈ us, occ2 u = 0) →
    occ2 (rcombT (us.map (sb c)) (var 0)) = 0
  | [], _ => by simp [rcombT, occ2]
  | u :: us, h => by
    simp only [List.map_cons, rcombT, occ2]
    rw [sb_occ2 c hc2 u (h u (by simp)), occ2_rcombT c hc2 us (fun v hv => h v (by simp [hv]))]
