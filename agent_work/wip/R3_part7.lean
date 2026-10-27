
/-! ### Handler-only variants: PAX (the next phase never opens c0') and PAMF (multi-wrapper with F(c0) not h1/h2) -/

/-- **THEOREM PAX.**  Single wrapper w = b0.c0: if the next phase never reaches a c0'-prefixed front, every
    p'-headed front has a y-free element or the bare y at position 3. -/
theorem pax_main (b0 c0 : T) (c : Nat) (hc2 : c ≠ 2) (hb0S : head b0 = S) (hc0S : head c0 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hnx1 : ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      ¬ wpre (sb c c0) f) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hy0' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hstep0 : step [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] =
      some ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    simp [step, head, hb0', args, BOT]
  have hBI : BI (sb c c0) ((args (sb c b0) ++ [sb c c0, var 0]) ++ BOT) := by
    refine ⟨args (sb c b0) ++ [sb c c0, var 0], rfl, ?_, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he
      · exact occ2_args _ hy0' e he
      · rw [he]; exact hy1'
      · rw [he]; simp [occ2]
    · rw [nbar_append]
      have h1 : barB (sb c c0) (sb c c0) = true := by
        simp [barB, (wpreB_iff _ _).2 (wpre_self _)]
      have h2 : barB (sb c c0) (var 0) = true := by simp [barB, head]
      simp [nbar, h1, h2]
  match m, hm with
  | 0, hm =>
    simp [run] at hm
    obtain ⟨hf0, _⟩ := hm
    rw [← hf0] at hf; simp [head, hb0'] at hf
  | m' + 1, hm =>
    have hm' := hm
    simp only [run] at hm
    rw [hstep0] at hm
    simp only at hm
    rcases pa_phase (sb c c0) _ hBI m' _ hm with hB | ⟨m1, L1, hlt, hr1, ⟨f1, b1, d1, R1, hL1, hwp⟩, _⟩
    · exact bi_x2 (sb c c0) f b d R hB
    · exfalso
      have : run (m1 + 1) [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some L1 := by
        simp only [run]; rw [hstep0]; exact hr1
      rw [hL1] at this
      exact hnx1 (m1 + 1) f1 b1 d1 R1 this hwp

/-- the generalised core with a bare-S innermost code: from [c0', p'] ++ B no p'-front, whatever B is -/
theorem core_bareS (c0' : T) (B : List T) (hc0' : head c0' = S)
    (hpost : ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
      run j (args c0' ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0) :
    ∀ (m : Nat) (f : T) (L : List T), run m ([c0', var 0] ++ B) = some (f :: L) → head f ≠ var 0 := by
  intro m f L hm
  match m, hm with
  | 0, hm =>
    simp [run] at hm; rw [← hm.1, hc0']; simp
  | m' + 1, hm =>
    match B, hm with
    | [], hm => simp [run, step] at hm
    | e :: B', hm =>
      simp only [List.cons_append, List.nil_append, run] at hm
      have hs : step (c0' :: var 0 :: e :: B') = some (args c0' ++ e :: app (var 0) e :: B') := by
        simp [step, hc0']
      rw [hs] at hm
      simp only at hm
      exact hpost e (app (var 0) e) B' m' f L hm

/-- **THEOREM PAMF.**  Theorem PAM with the replay hypothesis replaced by the handler-only condition 'the abstract
    run of args(c0) ++ [h1, h2] never calls h1 / h2' (paf_post), and the bottom condition replaced by
    'B0ok or b0 = S'.  Multi-wrapper handlers, innermost level vn = b0.c0. -/
theorem pamf_main (b0 c0 : T) (c h1 h2 : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hb0S : head b0 = S) (hc0S : head c0 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hf1 : occN h1 c0 = 0) (hf2 : occN h2 c0 = 0)
    (hNH : ∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g ≠ var h1 ∧ head g ≠ var h2)
    (L0 : List T) (h0 : ∀ e ∈ L0, guarded (app (app (sb c b0) (sb c c0)) (var 0)) e)
    (hB0 : b0 = S ∨ ∀ (m1 : Nat) (L1 L2 : List T), run m1 L0 = some L1 →
      (∀ e ∈ L1, guarded (app (app (sb c b0) (sb c c0)) (var 0)) e) →
      (∃ f b d R, L1 = f :: b :: d :: R ∧ wpre (app (app (sb c b0) (sb c c0)) (var 0)) f) →
      step L1 = some L2 → ∀ B, L2 = args (sb c b0) ++ [sb c c0, var 0] ++ B → B0ok B) :
    ∀ (m : Nat) (f b d : T) (R : List T), run m L0 = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hc0' : head (sb c c0) = S := sb_head c c0 hc0S
  have hy0' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hLnS : head (app (app (sb c b0) (sb c c0)) (var 0)) = S := by simp [head, hb0']
  have hpost := paf_post c0 c h1 h2 hc hh1 hh2 h12 hc0S hf1 hf2 hNH
  rcases guarded_phase _ hLnS L0 h0 m _ hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
  · exfalso
    have := guarded_head _ (by rw [hLnS]; simp) f (hG f (by simp))
    exact this hf
  · obtain ⟨f1, b1, d1, R1, hL1, hwp⟩ := hx1
    obtain ⟨us, hus⟩ := args_wpre _ hLnS f1 hwp
    have hf1S : head f1 = S := by rw [wpre_headeq _ f1 hwp]; exact hLnS
    have hs2' : step L1 = some (args (sb c b0) ++ [sb c c0, var 0] ++ (us ++ d1 :: app b1 d1 :: R1)) := by
      rw [hL1]; simp [step, hf1S, hus, args]
    rw [hs2'] at hs2
    injection hs2 with hs2
    subst hs2
    rcases hB0 with hbS | hB0
    · exfalso
      subst hbS
      have hnil : args (sb c S) = [] := by simp [sb, args]
      rw [hnil, List.nil_append] at hrest
      exact core_bareS (sb c c0) _ hc0' hpost (m - m1 - 1) f (b :: d :: R) hrest hf
    · have hBok := hB0 m1 L1 _ hr1 hg1 ⟨f1, b1, d1, R1, hL1, hwp⟩ hs2' _ rfl
      exact pa_core_g (sb c b0) (sb c c0) _ hBok hc0' hy0' hy1' hpost (m - m1 - 1) f b d R hrest hf
