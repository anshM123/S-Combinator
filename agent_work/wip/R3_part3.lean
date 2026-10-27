
/-! ### Theorem PAF: the single-wrapper replay WITHOUT phase-2 hypotheses -/

/-- occurrences of the atom var n -/
def occN (n : Nat) : T → Nat
  | S => 0
  | var m => if m = n then 1 else 0
  | app f x => occN n f + occN n x

theorem occN_args (n : Nat) : ∀ t : T, occN n t = 0 → ∀ s ∈ args t, occN n s = 0
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp only [occN] at h
    simp [args] at hs
    rcases hs with hs | hs
    · exact occN_args n f (by omega) s hs
    · subst hs; omega

/-- the substitution of the guard-free replay: p -> c, h1 -> e1, h2 -> e2, other atoms fixed -/
def sgH (c h1 h2 : Nat) (e1 e2 : T) : Nat → T :=
  fun n => if n = 0 then var c else if n = h1 then e1 else if n = h2 then e2 else var n

theorem asub_sgH_sb (c h1 h2 : Nat) (e1 e2 : T) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0) :
    ∀ t : T, occN h1 t = 0 → occN h2 t = 0 → asub (sgH c h1 h2 e1 e2) t = sb c t
  | S, _, _ => by simp [asub, sb]
  | var n, ha, hb => by
    by_cases h0 : n = 0
    · subst h0; simp [asub, sb, sgH]
    · have n1 : n ≠ h1 := by intro e; subst e; simp [occN] at ha
      have n2 : n ≠ h2 := by intro e; subst e; simp [occN] at hb
      simp [asub, sb, sgH, h0, n1, n2]
  | app f x, ha, hb => by
    simp only [occN] at ha hb
    simp [asub, sb, asub_sgH_sb c h1 h2 e1 e2 hh1 hh2 f (by omega) (by omega),
      asub_sgH_sb c h1 h2 e1 e2 hh1 hh2 x (by omega) (by omega)]

theorem sgH_head (c h1 h2 : Nat) (e1 e2 : T) (hc : c ≠ 0) (n : Nat) (n1 : n ≠ h1) (n2 : n ≠ h2) :
    head (sgH c h1 h2 e1 e2 n) ≠ var 0 ∧ head (sgH c h1 h2 e1 e2 n) ≠ S := by
  by_cases h0 : n = 0
  · subst h0; simp [sgH, head, hc]
  · simp [sgH, h0, n1, n2, head]

/-- **Post-x1 safety from the abstract outcome of c0.**  If the run of args(c0) ++ [h1, h2] (h1, h2 fresh atoms)
    never reaches a front headed by h1 or h2, then no run from args(c0[p:=c]) ++ [e1, e2, ...] ever reaches a front
    headed by var 0, whatever e1, e2 and the rest are.  No replay guard: both runs are images of one abstract run
    under atom substitutions. -/
theorem paf_post (c0 : T) (c h1 h2 : Nat) (hc : c ≠ 0) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0) (h12 : h1 ≠ h2)
    (hgS : head c0 = S) (hf1 : occN h1 c0 = 0) (hf2 : occN h2 c0 = 0)
    (hNH : ∀ (k : Nat) (f : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (f :: L) →
      head f ≠ var h1 ∧ head f ≠ var h2) :
    ∀ (e1 e2 : T) (B' : List T) (j : Nat) (f : T) (L : List T),
      run j (args (sb c c0) ++ e1 :: e2 :: B') = some (f :: L) → head f ≠ var 0 := by
  intro e1 e2 B' j f L hrun hf
  have hA : (args c0 ++ [var h1, var h2]).map (asub (sgH c h1 h2 e1 e2)) ++ B' =
      args (sb c c0) ++ e1 :: e2 :: B' := by
    rw [sb_args c c0 hgS]
    simp only [List.map_append, List.map_cons, List.map_nil]
    have hargs : (args c0).map (asub (sgH c h1 h2 e1 e2)) = (args c0).map (sb c) := by
      apply List.map_congr_left
      intro e he
      exact asub_sgH_sb c h1 h2 e1 e2 hh1 hh2 e (occN_args h1 c0 hf1 e he) (occN_args h2 c0 hf2 e he)
    rw [hargs]
    have hs1 : asub (sgH c h1 h2 e1 e2) (var h1) = e1 := by simp [asub, sgH, hh1]
    have hs2 : asub (sgH c h1 h2 e1 e2) (var h2) = e2 := by
      simp [asub, sgH, hh2, Ne.symm h12]
    rw [hs1, hs2]
    simp
  have hnHB : 2 ≤ nHB h1 h2 (args c0 ++ [var h1, var h2]) := by
    rw [nHB_append]; simp [nHB, isHB, head]
  rw [← hA] at hrun
  cases hj : run j (args c0 ++ [var h1, var h2]) with
  | some Aj =>
    have h1' := run_append j _ _ B' (asub_run (sgH c h1 h2 e1 e2) j _ _ hj)
    rw [hrun] at h1'
    have hlen := Nat.le_trans hnHB (nHB_run h1 h2 j _ Aj hj)
    match Aj, hj, h1', hlen with
    | [], _, _, hlen => simp [nHB] at hlen
    | f0 :: L0, hj, h1', _ =>
      simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at h1'
      obtain ⟨hff, _⟩ := h1'
      obtain ⟨hn1, hn2⟩ := hNH j f0 L0 hj
      rcases head_cases f0 with hS | ⟨n, hn⟩
      · have := asub_headS (sgH c h1 h2 e1 e2) f0 hS
        rw [← hff, hf] at this; simp at this
      · have n1 : n ≠ h1 := by intro e; subst e; exact hn1 hn
        have n2 : n ≠ h2 := by intro e; subst e; exact hn2 hn
        have := asub_headvar (sgH c h1 h2 e1 e2) n f0 hn
        rw [← hff, hf] at this
        exact (sgH_head c h1 h2 e1 e2 hc n n1 n2).1 this.symm
  | none =>
    obtain ⟨k, Ak, hk, hrk, hsk⟩ := run_first_none j _ hj
    obtain ⟨f0, rest, hAk, hf0⟩ := nHB_stop h1 h2 _ Ak k hnHB hrk hsk
    subst hAk
    obtain ⟨hn1, hn2⟩ := hNH k f0 rest hrk
    obtain ⟨n, hn⟩ : ∃ n, head f0 = var n := (head_cases f0).resolve_left hf0
    have n1 : n ≠ h1 := by intro e; subst e; exact hn1 hn
    have n2 : n ≠ h2 := by intro e; subst e; exact hn2 hn
    have hck := run_append k _ _ B' (asub_run (sgH c h1 h2 e1 e2) k _ _ hrk)
    have hne : head (asub (sgH c h1 h2 e1 e2) f0) ≠ S := by
      rw [asub_headvar _ n f0 hn]; exact (sgH_head c h1 h2 e1 e2 hc n n1 n2).2
    have hstep : step ((f0 :: rest).map (asub (sgH c h1 h2 e1 e2)) ++ B') = none := by
      simp only [List.map_cons, List.cons_append]
      exact step_head_ne _ _ hne
    have hk1 : run (k + 1) ((args c0 ++ [var h1, var h2]).map (asub (sgH c h1 h2 e1 e2)) ++ B') = none := by
      rw [run_add k 1, hck, Option.bind_some]
      simp only [run]
      rw [hstep]
    have := run_none_after (k + 1) j _ hk1 (by omega)
    rw [hrun] at this; simp at this

/-- **THEOREM PAF (single wrapper, no phase-2 hypothesis).**  Let w = b0.c0 (b0, c0 S-headed and free of y; b0 = S
    allowed) and let the abstract run of c0 on two fresh atoms never call them (F(c0) is not h1/h2).  Then in the
    generic run of the next datum w[p:=c].p' every p'-headed front has a y-free element or the bare y at position 3. -/
theorem paf_main (b0 c0 : T) (c h1 h2 : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hb0S : head b0 = S) (hc0S : head c0 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hf1 : occN h1 c0 = 0) (hf2 : occN h2 c0 = 0)
    (hNH : ∀ (k : Nat) (f : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (f :: L) →
      head f ≠ var h1 ∧ head f ≠ var h2) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 :=
  pa_core b0 c0 c hc2 hb0S hc0S hy0 hy1 (paf_post c0 c h1 h2 hc hh1 hh2 h12 hc0S hf1 hf2 hNH)
