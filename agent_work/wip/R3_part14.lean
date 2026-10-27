
def WOKp (h1 h2 : Nat) (b0 c0 : T) : Prop := head b0 = S ∧ head c0 = S ∧ occ2 b0 = 0 ∧ occ2 c0 = 0 ∧
  occN h1 c0 = 0 ∧ occN h2 c0 = 0 ∧ NHc c0 h1 h2

theorem wpreB_app' (w b d : T) (h : wpreB w b = true) : wpreB w (app b d) = true := by
  rw [wpreB_iff] at *; exact Or.inr h

/-- **The descent.**  From the start list of a level (wrapper b0.c0, remaining inner wrappers us, bottom B whose first
    element is y-free or the bare y and whose elements are guarded by the next level), every p'-headed front has a
    y-free element or the bare y at position 3, provided every level's c-code never calls its two holes. -/
theorem descend (c h1 h2 : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0) (h12 : h1 ≠ h2) :
    ∀ (us : List T) (b0 c0 : T) (B : List T), WOKp h1 h2 b0 c0 → (∀ u ∈ us, WOK h1 h2 u) → B0ok B →
    (us ≠ [] → ∀ e ∈ B, guarded (rcombT (us.map (sb c)) (var 0)) e) →
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m (args (sb c b0) ++ [sb c c0, rcombT (us.map (sb c)) (var 0)] ++ B) = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2
  | [], b0, c0, B, ⟨hb0S, hc0S, hy0, hy1, hf1, hf2, hNH⟩, _, hB, _ => by
    intro m f b d R hm hf
    have hpost := paf_post c0 c h1 h2 hc hh1 hh2 h12 hc0S hf1 hf2 hNH
    exact pa_core_g (sb c b0) (sb c c0) B hB (sb_head c c0 hc0S) (sb_occ2 c hc2 b0 hy0) (sb_occ2 c hc2 c0 hy1)
      hpost m f b d R (by simpa [rcombT] using hm) hf
  | u' :: us'', b0, c0, B, ⟨hb0S, hc0S, hy0, hy1, hf1, hf2, hNH⟩, hus, hB, hg => by
    intro m f b d R hm hf
    obtain ⟨b1, c1, hu', hb1S, hc1S, hy0', hy1', hf1', hf2', hNH'⟩ := hus u' (by simp)
    have hus'' : ∀ u ∈ us'', WOK h1 h2 u := fun u hu => hus u (by simp [hu])
    have hpost := paf_post c0 c h1 h2 hc hh1 hh2 h12 hc0S hf1 hf2 hNH
    -- the next level
    have hLn : rcombT ((u' :: us'').map (sb c)) (var 0) =
        app (app (sb c b1) (sb c c1)) (rcombT (us''.map (sb c)) (var 0)) := by
      simp [rcombT, hu', sb]
    generalize hLnext : rcombT ((u' :: us'').map (sb c)) (var 0) = Lnext at hm hg
    have hLnS : head Lnext = S := by rw [← hLnext, hLn]; simp [head, sb_head c b1 hb1S]
    have hc0'S : head (sb c c0) = S := sb_head c c0 hc0S
    let bar : T → Bool := fun t => wpreB (sb c c0) t || wpreB Lnext t
    have hbar : ∀ b' d', bar b' = true → bar (app b' d') = true := by
      intro b' d' hb'
      simp only [bar, Bool.or_eq_true] at hb' ⊢
      rcases hb' with hb' | hb'
      · exact Or.inl (wpreB_app' _ _ _ hb')
      · exact Or.inr (wpreB_app' _ _ _ hb')
    let Inv : List T → Prop := fun L => BIG bar B L ∧ ∀ e ∈ L, guarded Lnext e
    have hInv : ∀ f' b' d' R', Inv (f' :: b' :: d' :: R') → bar f' = false → head f' = S →
        Inv (args f' ++ d' :: app b' d' :: R') := by
      intro f' b' d' R' ⟨hBI, hG⟩ hbf hfS
      refine ⟨big2_step bar hbar B f' b' d' R' hBI hbf, ?_⟩
      have hnw : ¬ wpre Lnext f' := by
        intro hw
        have : wpreB Lnext f' = true := (wpreB_iff _ _).2 hw
        simp [bar, this] at hbf
      intro e he; simp at he
      rcases he with he | he | he | he
      · exact guarded_args Lnext f' (hG f' (by simp)) hfS hnw e he
      · rw [he]; exact hG d' (by simp)
      · rw [he]; exact Or.inr ⟨hG b' (by simp), hG d' (by simp)⟩
      · exact hG e (by simp [he])
    have hy0'' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
    have hy1'' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
    have hyL : occ2 Lnext = 0 := by
      rw [← hLnext]
      apply occ2_rcombT c hc2
      intro u hu; simp at hu
      rcases hu with hu | hu
      · rw [hu, hu']; simp [occ2, hy0', hy1']
      · obtain ⟨b2, c2, he, _, _, hy2, hy3, _⟩ := hus'' u hu
        rw [he]; simp [occ2, hy2, hy3]
    have hI0 : Inv (args (sb c b0) ++ [sb c c0, Lnext] ++ B) := by
      refine ⟨⟨args (sb c b0) ++ [sb c c0, Lnext], rfl, ?_, ?_⟩, ?_⟩
      · intro e he; simp at he
        rcases he with he | he | he
        · exact occ2_args _ hy0'' e he
        · rw [he]; exact hy1''
        · rw [he]; exact hyL
      · rw [nbarG_append]
        have e1 : bar (sb c c0) = true := by simp [bar, (wpreB_iff _ _).2 (wpre_self _)]
        have e2 : bar Lnext = true := by simp [bar, (wpreB_iff _ _).2 (wpre_self _)]
        simp [nbarG, e1, e2]
      · intro e he; simp at he
        rcases he with he | he | he | he
        · exact guarded_free Lnext e (occN_args 0 _ (sb_free0 c hc b0) e he)
        · rw [he]; exact guarded_free Lnext _ (sb_free0 c hc c0)
        · rw [he, ← hLnext, hLn]; exact Or.inl rfl
        · exact hg (by simp) e he
    rcases phaseQ bar Inv hInv _ hI0 m _ hm with ⟨_, hG⟩ | ⟨m1, L1, hlt, hr1, ⟨hBI1, hG1⟩, ⟨f1, b1', d1, R1, hL1, hbf1⟩, hrest⟩
    · exact absurd hf (guarded_head Lnext (by rw [hLnS]; simp) f (hG f (by simp)))
    · subst hL1
      have hmk : m - m1 = (m - m1 - 1) + 1 := by omega
      rw [hmk] at hrest
      simp only [run] at hrest
      by_cases hx1 : wpre (sb c c0) f1
      · exfalso
        obtain ⟨e1, e2, B', hs1⟩ := x1_open (sb c c0) f1 b1' d1 R1 hc0'S hx1
        rw [hs1] at hrest
        simp only at hrest
        exact hpost e1 e2 B' _ f _ hrest hf
      · have hx2 : wpre Lnext f1 := by
          simp only [bar, Bool.or_eq_true] at hbf1
          rcases hbf1 with h | h
          · exact absurd ((wpreB_iff _ _).1 h) hx1
          · exact (wpreB_iff _ _).1 h
        have hf1S : head f1 = S := by rw [wpre_headeq _ f1 hx2]; exact hLnS
        obtain ⟨us1, hus1, hgus1⟩ := guarded_prefix_args Lnext f1 hx2 (hG1 f1 (by simp))
        have hargsL : args Lnext = args (sb c b1) ++ [sb c c1, rcombT (us''.map (sb c)) (var 0)] := by
          rw [← hLnext, hLn]; simp [args]
        have hs2 : step (f1 :: b1' :: d1 :: R1) = some (args (sb c b1) ++
            [sb c c1, rcombT (us''.map (sb c)) (var 0)] ++ (us1 ++ d1 :: app b1' d1 :: R1)) := by
          simp [step, hf1S, hus1, hargsL]
        rw [hs2] at hrest
        simp only at hrest
        -- the new bottom
        have hyf1 : occ2 f1 = 0 := by
          obtain ⟨Tp, hTp, hyT, hnT⟩ := hBI1
          match Tp, hTp, hnT with
          | [], _, hnT => simp [nbarG] at hnT
          | t1 :: Tp', hTp, _ =>
            simp at hTp; rw [hTp.1]; exact hyT t1 (by simp)
        have hB' : B0ok (us1 ++ d1 :: app b1' d1 :: R1) := by
          intro e he
          cases us1 with
          | nil =>
            simp only [List.nil_append, List.head?_cons, Option.some.injEq] at he
            subst he
            exact big2_pos3 bar B hB f1 b1' _ R1 hBI1
          | cons u us1' =>
            simp only [List.cons_append, List.head?_cons, Option.some.injEq] at he
            subst he
            left
            exact occ2_args f1 hyf1 _ (by rw [hus1]; simp)
        have hfree' : occN 0 (app (sb c b1) (sb c c1)) = 0 := by
          simp [occN, sb_free0 c hc b1, sb_free0 c hc c1]
        have hg' : us'' ≠ [] → ∀ e ∈ us1 ++ d1 :: app b1' d1 :: R1,
            guarded (rcombT (us''.map (sb c)) (var 0)) e := by
          intro hne e he
          have hL2app : ∃ g z, rcombT (us''.map (sb c)) (var 0) = app g z := by
            match us'', hne with
            | v :: vs, _ => exact ⟨sb c v, rcombT (vs.map (sb c)) (var 0), by simp [rcombT]⟩
          have hmono : ∀ t, guarded Lnext t → guarded (rcombT (us''.map (sb c)) (var 0)) t := by
            intro t ht
            rw [← hLnext, hLn] at ht
            exact guarded_mono _ _ hfree' hL2app t ht
          simp at he
          rcases he with he | he | he | he
          · exact hmono e (hgus1 e he)
          · rw [he]; exact hmono _ (hG1 d1 (by simp))
          · rw [he]; exact hmono _ (Or.inr ⟨hG1 b1' (by simp), hG1 d1 (by simp)⟩)
          · exact hmono e (hG1 e (by simp [he]))
        exact descend c h1 h2 hc hc2 hh1 hh2 h12 us'' b1 c1 _ ⟨hb1S, hc1S, hy0', hy1', hf1', hf2', hNH'⟩ hus''
          hB' hg' (m - m1 - 1) f b d R (by simpa using hrest) hf

/-- **THEOREM NHALL.**  Let V = v1.(v2.(...(vn.y))) be a phase-2 handler (any number n >= 1 of wrappers) such that
    every wrapper v_j = b_j.c_j has S-headed y-free b_j, c_j and the abstract run of args(c_j) ++ [h1, h2] never
    calls h1 or h2.  Then in the next phase (datum V[y:=p', p:=c]) every p'-headed front has a y-free element or
    the bare y at position 3: no proper transfer.  The hypothesis concerns only the codes c_j of the handler. -/
theorem nhall_main (ws : List T) (c h1 h2 : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hws : ws ≠ []) (hall : ∀ u ∈ ws, WOK h1 h2 u) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [rcombT (ws.map (sb c)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  match ws, hws, hall with
  | u0 :: ws', _, hall =>
    obtain ⟨b0, c0, hu0, hb0S, hc0S, hy0, hy1, hf1, hf2, hNH⟩ := hall u0 (by simp)
    have hall' : ∀ u ∈ ws', WOK h1 h2 u := fun u hu => hall u (by simp [hu])
    have hD3 : rcombT ((u0 :: ws').map (sb c)) (var 0) =
        app (app (sb c b0) (sb c c0)) (rcombT (ws'.map (sb c)) (var 0)) := by
      simp [rcombT, hu0, sb]
    rw [hD3] at hm
    have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
    match m, hm with
    | 0, hm =>
      simp [run] at hm; rw [← hm.1] at hf; simp [head, hb0'] at hf
    | m' + 1, hm =>
      have hs : step [app (app (sb c b0) (sb c c0)) (rcombT (ws'.map (sb c)) (var 0)), var 1, var 2, var 3] =
          some (args (sb c b0) ++ [sb c c0, rcombT (ws'.map (sb c)) (var 0)] ++
            [var 2, app (var 1) (var 2), var 3]) := by
        simp [step, head, hb0', args]
      simp only [run] at hm
      rw [hs] at hm
      simp only at hm
      have hB : B0ok [var 2, app (var 1) (var 2), var 3] := by
        intro e he; simp at he; subst he; right; rfl
      have hg : ws' ≠ [] → ∀ e ∈ [var 2, app (var 1) (var 2), var 3],
          guarded (rcombT (ws'.map (sb c)) (var 0)) e := by
        intro _ e he; simp at he
        rcases he with he | he | he <;> (subst he; apply guarded_free; simp [occN])
      exact descend c h1 h2 hc hc2 hh1 hh2 h12 ws' b0 c0 _ ⟨hb0S, hc0S, hy0, hy1, hf1, hf2, hNH⟩ hall' hB hg
        m' f b d R hm hf
