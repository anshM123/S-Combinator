
/-! Part 3: the phase invariant and Theorem PA -/

theorem runOK_mono (w : T) : ∀ (k j : Nat) (L : List T), runOK w k L → j ≤ k → runOK w j L
  | _, 0, _, _, _ => trivial
  | 0, j + 1, _, _, hj => by omega
  | k + 1, j + 1, L, hok, hj => by
    obtain ⟨hG, hrest⟩ := hok
    refine ⟨hG, ?_⟩
    cases hs : step L with
    | none => trivial
    | some L' => rw [hs] at hrest; exact runOK_mono w k j L' hrest (by omega)

theorem wpre_self (w : T) : wpre w w := by
  cases w <;> simp [wpre]

theorem sb_occ2 (c : Nat) (hc2 : c ≠ 2) : ∀ t : T, occ2 t = 0 → occ2 (sb c t) = 0
  | S, _ => by simp [sb, occ2]
  | var n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [sb, occ2, hc2]
    · simp [sb, h0]; simpa [occ2] using h
  | app f x, h => by
    simp only [occ2] at h
    simp only [sb, occ2]
    rw [sb_occ2 c hc2 f (by omega), sb_occ2 c hc2 x (by omega)]

theorem pa_phase (c0' : T) (L0 : List T) (h0 : BI c0' L0) : ∀ (m : Nat) (L : List T), run m L0 = some L →
    BI c0' L ∨ ∃ m1 L1, m1 < m ∧ run m1 L0 = some L1 ∧
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
        | some L' => rw [hs] at h1; simp [run] at h1; rw [h1]
      rcases pa_phase c0' L0 h0 m Lm hm with hB | ⟨m1, L1, hlt, hr1, hx1, hrest⟩
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
              exact bi_step c0' f b d R hB hfS hbf
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

/-- **Theorem PA.**  Let the innermost single wrapper of a phase-2 handler be w = b0.c0 (b0, c0 S-headed and free
    of y), glued onto y in pattern alpha, i.e. by the step [c0, w, y] ++ R0, after which phase 2 continues from the
    top part args c0 ++ [y, w.y].  Assume this top part reaches a p-headed front (the TRANSFER) after k steps
    under the replay guards (no (w.y)-prefixed front, w.y never re-created).  Then in the generic run of the next
    phase's datum w[p:=c].p' (here p' = var 0 and c a frozen atom) every p'-headed front has at position 3 a
    y-free element or the bare y: the next phase NEVER makes a proper transfer. -/
theorem pa_main (b0 c0 : T) (c : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hb0S : head b0 = S) (hc0S : head c0 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0) (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args c0 ++ [var 2, app (app b0 c0) (var 2)]) = some (a' :: rest))
    (hok : runOK (app (app b0 c0) (var 2)) k (args c0 ++ [var 2, app (app b0 c0) (var 2)]))
    (hp : head a' = var 0) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hc0' : head (sb c c0) = S := sb_head c c0 hc0S
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
    simp only [run] at hm
    rw [hstep0] at hm
    simp only at hm
    rcases pa_phase (sb c c0) _ hBI m' _ hm with hB | ⟨m1, L1, hlt, _, ⟨f1, b1, d1, R1, hL1, hwp⟩, hrest⟩
    · exact bi_x2 (sb c c0) f b d R hB
    · exfalso
      obtain ⟨e1, e2, B', hs1⟩ := x1_open (sb c c0) f1 b1 d1 R1 hc0' hwp
      subst hL1
      have hj : m' - m1 = (m' - m1 - 1) + 1 := by omega
      rw [hj] at hrest
      simp only [run] at hrest
      rw [hs1] at hrest
      simp only at hrest
      have himg := pa_image b0 c0 e1 e2 c hc0S hy1
      have hM0 : args (sb c c0) ++ e1 :: e2 :: B' =
          (args c0 ++ [var 2, app (app b0 c0) (var 2)]).map (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) ++ B' := by
        rw [himg]; simp
      rw [hM0] at hrest
      have hwyS : head (app (app b0 c0) (var 2)) = S := by simp [head, hb0S]
      have hna' : ¬ wpre (app (app b0 c0) (var 2)) a' := by
        intro hw; have := wpre_headeq _ a' hw; rw [hp, hwyS] at this; simp at this
      have hca' : head (rho (app (app b0 c0) (var 2)) e2 (sgE c e1) a') = var c := by
        rw [rho_headvar _ _ _ 0 a' hna' hp]; simp [sgE, head]
      by_cases hjk : m' - m1 - 1 ≤ k
      · obtain ⟨Pj, hPj, hPk⟩ := run_prefix k (m' - m1 - 1) _ _ hrun hjk
        have hokj := runOK_mono _ k (m' - m1 - 1) _ hok hjk
        have hrep := replay_run_gen (app (app b0 c0) (var 2)) e2 (sgE c e1) (m' - m1 - 1) _ _ hokj hPj
        have happ := run_append (m' - m1 - 1) _ _ B' hrep
        rw [hrest] at happ
        injection happ with happ
        match Pj, happ, hPk, hPj with
        | [], happ, hPk, _ =>
          cases hkj : k - (m' - m1 - 1) with
          | zero => rw [hkj] at hPk; simp [run] at hPk
          | succ n => rw [hkj] at hPk; simp [run, step] at hPk
        | pj :: pjs, happ, hPk, hPj =>
          simp at happ
          obtain ⟨hfj, _⟩ := happ
          by_cases hjk' : m' - m1 - 1 = k
          · have h0k : k - (m' - m1 - 1) = 0 := by omega
            rw [h0k] at hPk; simp [run] at hPk
            obtain ⟨hpj, _⟩ := hPk
            rw [hpj] at hfj
            rw [← hfj, hca'] at hf
            injection hf with hf; exact hc hf
          · have hok2 := runOK_after _ (m' - m1 - 1) k _ _ hok hPj hjk
            have hk1 : k - (m' - m1 - 1) = (k - (m' - m1 - 1) - 1) + 1 := by omega
            rw [hk1] at hok2 hPk
            have hG := runOK_G _ _ _ hok2
            simp only [run] at hPk
            match pjs, hG, hPk with
            | q1 :: q2 :: qs, hG, hPk =>
              obtain ⟨hnw, _⟩ := hG
              by_cases hpS : head pj = S
              · have := rho_headS _ e2 (sgE c e1) pj hnw hpS
                rw [hfj, hf] at this; simp at this
              · simp [step, hpS] at hPk
            | [], _, hPk => simp [step] at hPk
            | [_], _, hPk => simp [step] at hPk
      · have hrep := replay_run_gen (app (app b0 c0) (var 2)) e2 (sgE c e1) k _ _ hok hrun
        have happ := run_append k _ _ B' hrep
        have hsplit := run_add (k + 1) ((m' - m1 - 1) - (k + 1)) ((args c0 ++ [var 2, app (app b0 c0) (var 2)]).map
          (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) ++ B')
        rw [show k + 1 + ((m' - m1 - 1) - (k + 1)) = m' - m1 - 1 by omega, hrest] at hsplit
        have hk1 := run_add k 1 ((args c0 ++ [var 2, app (app b0 c0) (var 2)]).map
          (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) ++ B')
        rw [happ] at hk1
        have hstuck : run 1 (List.map (rho (app (app b0 c0) (var 2)) e2 (sgE c e1)) (a' :: rest) ++ B') = none := by
          simp [run, step, hca']
        rw [hk1] at hsplit
        simp [hstuck] at hsplit

#print axioms pa_main
