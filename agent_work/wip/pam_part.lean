
/-! ## Theorem PAM: Theorem PA for MULTI-WRAPPER handlers, at the innermost level.
    p' occurs in the next datum only inside copies of its innermost level Ln = vn'.p'; until an Ln-prefixed
    element is opened every element is 'guarded' (no p'-front); the first such opening yields
    args(b0') ++ [c0', p'] ++ B, and from there the barrier phase and the post-x1 replay of phase 2's continuation from
    vn's glue step apply exactly as in Theorem PA, provided the element B0 right below p' is y-free or the bare y. -/

def guarded (Lv : T) : T → Prop
  | S => True
  | var n => n ≠ 0
  | app f x => app f x = Lv ∨ (guarded Lv f ∧ guarded Lv x)

theorem guarded_head (Lv : T) (hL : head Lv ≠ var 0) : ∀ t : T, guarded Lv t → head t ≠ var 0
  | S, _ => by simp [head]
  | var n, h => by simp [guarded] at h; simp [head]; exact h
  | app f x, h => by
    rcases h with h | ⟨hf, _⟩
    · rw [h]; exact hL
    · simp [head]; exact guarded_head Lv hL f hf

theorem guarded_args (Lv : T) : ∀ t : T, guarded Lv t → head t = S → ¬ wpre Lv t → ∀ s ∈ args t, guarded Lv s
  | S, _, _, _, s, hs => by simp [args] at hs
  | var _, _, hh, _, _, _ => by simp [head] at hh
  | app f x, h, hh, hn, s, hs => by
    have h1 : app f x ≠ Lv := fun e => hn (Or.inl e)
    have h2 : ¬ wpre Lv f := fun e => hn (Or.inr e)
    rcases h with h | ⟨hf, hx⟩
    · exact absurd h h1
    · simp [args] at hs
      rcases hs with hs | hs
      · exact guarded_args Lv f hf (by simpa [head] using hh) h2 s hs
      · subst hs; exact hx

/-- a bottom is admissible if its first element is y-free or the bare y -/
def B0ok (B : List T) : Prop := ∀ e, B.head? = some e → occ2 e = 0 ∨ e = var 2

def BIg (c0' : T) (B : List T) (L : List T) : Prop :=
  ∃ Tp : List T, L = Tp ++ B ∧ (∀ e ∈ Tp, occ2 e = 0) ∧ 2 ≤ nbar c0' Tp

theorem big_step (c0' : T) (B : List T) (a b d : T) (R : List T) (hI : BIg c0' B (a :: b :: d :: R))
    (hna : barB c0' a = false) : BIg c0' B (args a ++ d :: app b d :: R) := by
  obtain ⟨Tp, hL, hy, hn⟩ := hI
  match Tp, hL, hy, hn with
  | [], _, _, hn => simp [nbar] at hn
  | [a1], _, _, hn => simp [nbar] at hn; split at hn <;> omega
  | [a1, b1], hL, _, hn =>
    simp at hL; obtain ⟨rfl, _⟩ := hL
    simp [nbar, hna] at hn; split at hn <;> omega
  | a1 :: b1 :: d1 :: R1, hL, hy, hn =>
    simp at hL
    obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    refine ⟨args a ++ d :: app b d :: R1, by rw [hR]; simp, ?_, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he | he
      · exact occ2_args a (hy a (by simp)) e he
      · rw [he]; exact hy d (by simp)
      · rw [he]; simp only [occ2]; have := hy b (by simp); have := hy d (by simp); omega
      · exact hy e (by simp [he])
    · rw [nbar_append]
      have hbd : (if barB c0' b = true then 1 else 0) ≤ (if barB c0' (app b d) = true then 1 else 0) := by
        by_cases hb : barB c0' b = true
        · simp [hb, barB_app c0' b d hb]
        · simp [hb]
      simp only [nbar, hna] at hn ⊢
      simp at hn ⊢
      omega

theorem big_x2 (c0' : T) (B : List T) (hB : B0ok B) (a b d : T) (R : List T)
    (hI : BIg c0' B (a :: b :: d :: R)) : occ2 d = 0 ∨ d = var 2 := by
  obtain ⟨Tp, hL, hy, hn⟩ := hI
  match Tp, hL, hy, hn with
  | [], _, _, hn => simp [nbar] at hn
  | [a1], _, _, hn => simp [nbar] at hn; split at hn <;> omega
  | [a1, b1], hL, _, _ =>
    simp at hL
    obtain ⟨_, _, hB2⟩ := hL
    exact hB d (by rw [← hB2]; simp)
  | a1 :: b1 :: d1 :: R1, hL, hy, _ =>
    simp at hL; obtain ⟨_, _, rfl, _⟩ := hL
    left; exact hy d (by simp)

theorem pa_phase_g (c0' : T) (B : List T) (L0 : List T) (h0 : BIg c0' B L0) :
    ∀ (m : Nat) (L : List T), run m L0 = some L →
    BIg c0' B L ∨ ∃ m1 L1, m1 < m ∧ run m1 L0 = some L1 ∧
      (∃ f b d R, L1 = f :: b :: d :: R ∧ wpre c0' f) ∧ run (m - m1) L1 = some L
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
      rcases pa_phase_g c0' B L0 h0 m Lm hm with hB | ⟨m1, L1, hlt, hr1, hx1, hrest⟩
      · match Lm, hB, hstep, hm with
        | f :: b :: d :: R, hB, hstep, hm =>
          simp only [step] at hstep
          split at hstep
          · rename_i hfS
            by_cases hb : barB c0' f = true
            · right
              have hwp : wpre c0' f := by
                simp only [barB, Bool.or_eq_true, decide_eq_true_eq] at hb
                rcases hb with hb | hb
                · exact (wpreB_iff c0' f).1 hb
                · rw [hfS] at hb; simp at hb
              refine ⟨m, f :: b :: d :: R, by omega, hm, ⟨f, b, d, R, rfl, hwp⟩, ?_⟩
              simpa using h1
            · left
              have hbf : barB c0' f = false := by simpa using hb
              injection hstep with hstep; subst hstep
              exact big_step c0' B f b d R hB hbf
          · exact absurd hstep (by simp)
        | [], _, hstep, _ => simp [step] at hstep
        | [_], _, hstep, _ => simp [step] at hstep
        | [_, _], _, hstep, _ => simp [step] at hstep
      · right
        refine ⟨m1, L1, by omega, hr1, hx1, ?_⟩
        have hadd2 := run_add (m - m1) 1 L1
        rw [hrest] at hadd2
        rw [show m + 1 - m1 = (m - m1) + 1 by omega, hadd2]
        simpa using h1

/-- the generalised core: from any list args(b0') ++ [c0', p'] ++ B with an admissible bottom B -/
theorem pa_core_g (b0' c0' : T) (B : List T) (hB : B0ok B) (hc0' : head c0' = S)
    (hy0' : occ2 b0' = 0) (hy1' : occ2 c0' = 0)
    (hpost : ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
      run j (args c0' ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m (args b0' ++ [c0', var 0] ++ B) = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hBI : BIg c0' B (args b0' ++ [c0', var 0] ++ B) := by
    refine ⟨args b0' ++ [c0', var 0], rfl, ?_, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he
      · exact occ2_args _ hy0' e he
      · rw [he]; exact hy1'
      · rw [he]; simp [occ2]
    · rw [nbar_append]
      have h1 : barB c0' c0' = true := by simp [barB, (wpreB_iff _ _).2 (wpre_self _)]
      have h2 : barB c0' (var 0) = true := by simp [barB, head]
      simp [nbar, h1, h2]
  rcases pa_phase_g c0' B _ hBI m _ hm with hB' | ⟨m1, L1, hlt, _, ⟨f1, b1, d1, R1, hL1, hwp⟩, hrest⟩
  · exact big_x2 c0' B hB f b d R hB'
  · exfalso
    obtain ⟨e1, e2, B', hs1⟩ := x1_open c0' f1 b1 d1 R1 hc0' hwp
    subst hL1
    have hj : m - m1 = (m - m1 - 1) + 1 := by omega
    rw [hj] at hrest
    simp only [run] at hrest
    rw [hs1] at hrest
    simp only at hrest
    exact hpost e1 e2 B' _ f _ hrest hf

/-- the guarded phase: until an Ln-prefixed front is opened no front is p'-headed -/
theorem guarded_phase (Ln : T) (hLnS : head Ln = S) (L0 : List T) (h0 : ∀ e ∈ L0, guarded Ln e) :
    ∀ (m : Nat) (L : List T), run m L0 = some L →
    (∀ e ∈ L, guarded Ln e) ∨ ∃ m1 L1 L2, m1 < m ∧ run m1 L0 = some L1 ∧ (∀ e ∈ L1, guarded Ln e) ∧
      (∃ f b d R, L1 = f :: b :: d :: R ∧ wpre Ln f) ∧ step L1 = some L2 ∧ run (m - m1 - 1) L2 = some L
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
      rcases guarded_phase Ln hLnS L0 h0 m Lm hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
      · match Lm, hG, hstep, hm with
        | a :: b :: d :: R, hG, hstep, hm =>
          simp only [step] at hstep
          split at hstep
          · rename_i haS
            by_cases hpre : wpre Ln a
            · right
              refine ⟨m, a :: b :: d :: R, L, by omega, hm, hG, ⟨a, b, d, R, rfl, hpre⟩, ?_, by simp [run]⟩
              simp [step, haS] at hstep ⊢; exact hstep
            · left
              injection hstep with hstep; subst hstep
              intro e he; simp at he
              rcases he with he | he | he | he
              · exact guarded_args Ln a (hG a (by simp)) haS hpre e he
              · rw [he]; exact hG d (by simp)
              · rw [he]; exact Or.inr ⟨hG b (by simp), hG d (by simp)⟩
              · exact hG e (by simp [he])
          · exact absurd hstep (by simp)
        | [], _, hstep, _ => simp [step] at hstep
        | [_], _, hstep, _ => simp [step] at hstep
        | [_, _], _, hstep, _ => simp [step] at hstep
      · right
        refine ⟨m1, L1, L2, by omega, hr1, hg1, hx1, hs2, ?_⟩
        have hadd2 := run_add (m - m1 - 1) 1 L2
        rw [hrest] at hadd2
        rw [show m + 1 - m1 - 1 = (m - m1 - 1) + 1 by omega, hadd2]
        simpa using h1

/-- **Theorem PAM.**  Let the innermost wrapper of a (possibly multi-wrapper) phase-2 handler be vn = b0.c0, glued in
    pattern alpha, with phase 2's continuation from that glue (top part args c0 ++ [y, vn.y]) reaching its TRANSFER
    after k guarded steps.  Let L0 be the start of the next phase, in which every occurrence of p' = var 0 lies inside
    an occurrence of the innermost level Ln = vn[p:=c].p' (true for the datum V[y:=p', p:=c]).  If the element right
    below p' after every opening of an Ln-prefixed front is y-free or the bare y (hypothesis hB0), then every
    p'-headed front of the next phase has a y-free element or the bare y at position 3: no proper transfer. -/
theorem pam_main (b0 c0 : T) (c : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hb0S : head b0 = S) (hc0S : head c0 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0) (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args c0 ++ [var 2, app (app b0 c0) (var 2)]) = some (a' :: rest))
    (hok : runOK (app (app b0 c0) (var 2)) k (args c0 ++ [var 2, app (app b0 c0) (var 2)]))
    (hp : head a' = var 0) (L0 : List T)
    (h0 : ∀ e ∈ L0, guarded (app (app (sb c b0) (sb c c0)) (var 0)) e)
    (hB0 : ∀ (m1 : Nat) (L1 L2 : List T), run m1 L0 = some L1 →
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
  rcases guarded_phase _ hLnS L0 h0 m _ hm with hG | ⟨m1, L1, L2, hlt, hr1, hg1, hx1, hs2, hrest⟩
  · exfalso
    have := guarded_head _ (by rw [hLnS]; simp) f (hG f (by simp))
    exact this hf
  · obtain ⟨f1, b1, d1, R1, hL1, hwp⟩ := hx1
    -- the opened element releases args(vn') ++ [p'] ++ u
    obtain ⟨us, hus⟩ := args_wpre _ hLnS f1 hwp
    have hf1S : head f1 = S := by rw [wpre_headeq _ f1 hwp]; exact hLnS
    have hs2' : step L1 = some (args (sb c b0) ++ [sb c c0, var 0] ++ (us ++ d1 :: app b1 d1 :: R1)) := by
      rw [hL1]; simp [step, hf1S, hus, args]
    rw [hs2'] at hs2
    injection hs2 with hs2
    subst hs2
    have hBok := hB0 m1 L1 _ hr1 hg1 ⟨f1, b1, d1, R1, hL1, hwp⟩ hs2' _ rfl
    have hpost : ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
        run j (args (sb c c0) ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0 := by
      have hwy2 : var 2 ≠ app (app b0 c0) (var 2) := by intro h; cases h
      have hwyh : head (app (app b0 c0) (var 2)) ≠ var 0 := by simp [head, hb0S]
      have hsz : size c0 < size (app (app b0 c0) (var 2)) := by simp [size]; omega
      exact post_replay _ c0 c hc hc0S hy1 hsz hwy2 hwyh k a' rest hrun hok hp
    exact pa_core_g (sb c b0) (sb c c0) _ hBok hc0' hy0' hy1' hpost (m - m1 - 1) f b d R hrest hf

#print axioms pa_main
#print axioms pb_main
#print axioms pam_main
