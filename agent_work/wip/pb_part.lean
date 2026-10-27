
/-! ## Theorem PB (pattern beta with c0 = S.a1) and the reusable pieces: post-x1 replay for a general first code g,
    and the barrier phase with an abstract post-x1 safety hypothesis. -/

theorem pa_image_gen (wy g e1 e2 : T) (c : Nat) (hS : head g = S) (hy : occ2 g = 0)
    (hsz : size g < size wy) (hwy2 : var 2 ≠ wy) :
    (args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) = args (sb c g) ++ [e1, e2] := by
  rw [sb_args c g hS]
  simp only [List.map_append, List.map_cons, List.map_nil]
  have hargs : (args g).map (rho wy e2 (sgE c e1)) = (args g).map (sb c) := by
    apply List.map_congr_left
    intro e he
    have hsz' : size e < size wy := by
      have := size_args g e he
      omega
    rw [rho_small _ _ _ e hsz']
    exact asub_sgE_noy c e1 e (occ2_args g hy e he)
  rw [hargs, rho_self]
  have h2 : rho wy e2 (sgE c e1) (var 2) = e1 := by
    simp [rho, hwy2, sgE]
  simp [h2]

/-- **Post-x1 replay.**  If the phase-2 top part args g ++ [y, wy] reaches a p-headed front after k guarded steps,
    then no run from args(g[p:=c]) ++ [e1, e2, ...] ever reaches a front headed by var 0 (it replays phase 2 and
    stops at a c-headed front). -/
theorem post_replay (wy g : T) (c : Nat) (hc : c ≠ 0) (hgS : head g = S) (hgy : occ2 g = 0)
    (hsz : size g < size wy) (hwy2 : var 2 ≠ wy) (hwyh : head wy ≠ var 0)
    (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args g ++ [var 2, wy]) = some (a' :: rest))
    (hok : runOK wy k (args g ++ [var 2, wy])) (hp : head a' = var 0) :
    ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
      run j (args (sb c g) ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0 := by
  intro e1 e2 B' j f L hrest hf
  have himg := pa_image_gen wy g e1 e2 c hgS hgy hsz hwy2
  have hM0 : args (sb c g) ++ e1 :: e2 :: B' = (args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) ++ B' := by
    rw [himg]; simp
  rw [hM0] at hrest
  have hna' : ¬ wpre wy a' := by
    intro hw; have := wpre_headeq _ a' hw; rw [hp] at this; exact hwyh this.symm
  have hca' : head (rho wy e2 (sgE c e1) a') = var c := by
    rw [rho_headvar _ _ _ 0 a' hna' hp]; simp [sgE, head]
  by_cases hjk : j ≤ k
  · obtain ⟨Pj, hPj, hPk⟩ := run_prefix k j _ _ hrun hjk
    have hokj := runOK_mono _ k j _ hok hjk
    have hrep := replay_run_gen wy e2 (sgE c e1) j _ _ hokj hPj
    have happ := run_append j _ _ B' hrep
    rw [hrest] at happ
    injection happ with happ
    match Pj, happ, hPk, hPj with
    | [], happ, hPk, _ =>
      cases hkj : k - j with
      | zero => rw [hkj] at hPk; simp [run] at hPk
      | succ n => rw [hkj] at hPk; simp [run, step] at hPk
    | pj :: pjs, happ, hPk, hPj =>
      simp at happ
      obtain ⟨hfj, _⟩ := happ
      by_cases hjk' : j = k
      · have h0k : k - j = 0 := by omega
        rw [h0k] at hPk; simp [run] at hPk
        obtain ⟨hpj, _⟩ := hPk
        rw [hpj] at hfj
        rw [hfj, hca'] at hf
        injection hf with hf; exact hc hf
      · have hok2 := runOK_after _ j k _ _ hok hPj hjk
        have hk1 : k - j = (k - j - 1) + 1 := by omega
        rw [hk1] at hok2 hPk
        have hG := runOK_G _ _ _ hok2
        simp only [run] at hPk
        match pjs, hG, hPk with
        | q1 :: q2 :: qs, hG, hPk =>
          obtain ⟨hnw, _⟩ := hG
          by_cases hpS : head pj = S
          · have := rho_headS _ e2 (sgE c e1) pj hnw hpS
            rw [← hfj, hf] at this; simp at this
          · simp [step, hpS] at hPk
        | [], _, hPk => simp [step] at hPk
        | [_], _, hPk => simp [step] at hPk
  · have hrep := replay_run_gen wy e2 (sgE c e1) k _ _ hok hrun
    have happ := run_append k _ _ B' hrep
    have hsplit := run_add (k + 1) (j - (k + 1)) ((args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) ++ B')
    rw [show k + 1 + (j - (k + 1)) = j by omega, hrest] at hsplit
    have hk1 := run_add k 1 ((args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) ++ B')
    rw [happ] at hk1
    have hstuck : run 1 (List.map (rho wy e2 (sgE c e1)) (a' :: rest) ++ B') = none := by
      have hne : head (rho wy e2 (sgE c e1) a') ≠ S := by rw [hca']; simp
      simp only [List.map_cons, List.cons_append, run]
      rw [step_head_ne _ _ hne]
    have hk1' : run (k + 1) ((args g ++ [var 2, wy]).map (rho wy e2 (sgE c e1)) ++ B') = none := by
      rw [hk1]; simpa using hstuck
    rw [hk1'] at hsplit
    simp at hsplit

/-- **Barrier phase with an abstract post-x1 safety.**  For the next-phase datum (b0'.c0').p', if no run from
    args(c0') ++ [e1, e2, ...] ever reaches a p'-headed front, then every p'-headed front of the phase has a y-free
    element or the bare y at position 3. -/
theorem pa_core (b0 c0 : T) (c : Nat) (hc2 : c ≠ 2) (hb0S : head b0 = S) (hc0S : head c0 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hpost : ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
      run j (args (sb c c0) ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0) :
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
      exact hpost e1 e2 B' _ f _ hrest hf

/-- **Theorem PB (pattern beta, c0 = S.a1).**  If the single wrapper is w = b0.(S.a1) and it was glued onto y by the
    step [a1, w, y] (a1 released just above w), and the phase-2 continuation from that glue (top part
    args a1 ++ [y, w.y]) reaches a p-headed front after k guarded steps, then the next phase never makes a proper
    transfer. -/
theorem pb_main (b0 a1 : T) (c : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hb0S : head b0 = S) (ha1S : head a1 = S)
    (hy0 : occ2 b0 = 0) (hy1 : occ2 a1 = 0) (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args a1 ++ [var 2, app (app b0 (app S a1)) (var 2)]) = some (a' :: rest))
    (hok : runOK (app (app b0 (app S a1)) (var 2)) k (args a1 ++ [var 2, app (app b0 (app S a1)) (var 2)]))
    (hp : head a' = var 0) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c (app S a1))) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  have hc0S : head (app S a1) = S := by simp [head]
  have hy1' : occ2 (app S a1) = 0 := by simp [occ2]; exact hy1
  apply pa_core b0 (app S a1) c hc2 hb0S hc0S hy0 hy1'
  intro e1 e2 B' j f L hrun' hf
  have ha1' : head (sb c a1) = S := sb_head c a1 ha1S
  have hargs : args (sb c (app S a1)) = [sb c a1] := by simp [sb, args]
  rw [hargs] at hrun'
  match j, hrun' with
  | 0, hrun' =>
    simp [run] at hrun'
    obtain ⟨hf0, _⟩ := hrun'
    rw [← hf0, ha1'] at hf; simp at hf
  | j' + 1, hrun' =>
    have hs : step (sb c a1 :: e1 :: e2 :: B') = some (args (sb c a1) ++ e2 :: app e1 e2 :: B') := by
      simp [step, ha1']
    simp only [List.singleton_append, run] at hrun'
    rw [hs] at hrun'
    simp only at hrun'
    have hwy2 : var 2 ≠ app (app b0 (app S a1)) (var 2) := by intro h; cases h
    have hwyh : head (app (app b0 (app S a1)) (var 2)) ≠ var 0 := by simp [head, hb0S]
    have hsz : size a1 < size (app (app b0 (app S a1)) (var 2)) := by simp [size]; omega
    exact post_replay _ a1 c hc ha1S hy1 hsz hwy2 hwyh k a' rest hrun hok hp e2 (app e1 e2) B' j' f _ hrun' hf

#print axioms pa_main
#print axioms post_replay
#print axioms pa_core
#print axioms pb_main
