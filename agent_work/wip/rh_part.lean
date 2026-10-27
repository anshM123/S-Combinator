
/-! ## The replayed handler is trivial (toward D3).
    Strengthened barrier invariant BIv: the top part above BOT is y-free, has >= 2 barriers AND contains a
    p'-headed element (the p'-barrier is never destroyed).  At the first c0'-prefixed front the element e2 that the
    replay substitutes for the handler w.y is y-free, or the bare y, or (p'-headed).y.  Consequently the datum that
    the re-executed frozen value would receive in the Church-chain model, e2[y := p'', p' := c'], has no live
    predecessor, or is the bare p'', or is frozen-headed: it cannot start a further proper transfer. -/

def BIv (c0' : T) (L : List T) : Prop :=
  ∃ Tp : List T, L = Tp ++ BOT ∧ (∀ e ∈ Tp, occ2 e = 0) ∧ 2 ≤ nbar c0' Tp ∧ ∃ e ∈ Tp, head e = var 0

theorem biv_bi (c0' : T) (L : List T) (h : BIv c0' L) : BI c0' L := by
  obtain ⟨Tp, h1, h2, h3, _⟩ := h
  exact ⟨Tp, h1, h2, h3⟩

theorem biv_step (c0' : T) (a b d : T) (R : List T) (hI : BIv c0' (a :: b :: d :: R)) (hS : head a = S)
    (hna : barB c0' a = false) : BIv c0' (args a ++ d :: app b d :: R) := by
  obtain ⟨Tp, hL, hy, hn, ⟨e0, he0, hh0⟩⟩ := hI
  obtain ⟨Tp', hL', hy', hn'⟩ := bi_step c0' a b d R ⟨Tp, hL, hy, hn⟩ hS hna
  refine ⟨Tp', hL', hy', hn', ?_⟩
  -- Tp = a :: b :: d :: R1 (as in bi_step); Tp' = args a ++ d :: app b d :: R1
  match Tp, hL, he0, hn with
  | [], _, he0, _ => simp at he0
  | [a1], _, _, hn => simp [nbar] at hn; split at hn <;> omega
  | [a1, b1], hL, _, hn =>
    simp at hL; obtain ⟨rfl, _⟩ := hL
    simp [nbar, hna] at hn; split at hn <;> omega
  | a1 :: b1 :: d1 :: R1, hL, he0, _ =>
    simp at hL
    obtain ⟨rfl, rfl, rfl, hR⟩ := hL
    have hTp' : Tp' = args a ++ d :: app b d :: R1 := by
      have : Tp' ++ BOT = (args a ++ d :: app b d :: R1) ++ BOT := by rw [← hL', hR]; simp
      exact List.append_cancel_right this
    rw [hTp']
    simp at he0
    rcases he0 with he0 | he0 | he0 | he0
    · rw [he0, hS] at hh0; simp at hh0
    · exact ⟨app b d, by simp, by rw [he0] at hh0; simpa [head] using hh0⟩
    · exact ⟨d, by simp, by rw [← he0]; exact hh0⟩
    · exact ⟨e0, by simp [he0], hh0⟩

theorem pa_phase_v (c0' : T) (L0 : List T) (h0 : BIv c0' L0) : ∀ (m : Nat) (L : List T), run m L0 = some L →
    BIv c0' L ∨ ∃ m1 L1, m1 < m ∧ run m1 L0 = some L1 ∧ BIv c0' L1 ∧
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
      rcases pa_phase_v c0' L0 h0 m Lm hm with hB | ⟨m1, L1, hlt, hr1, hb1, hx1, hrest⟩
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
              refine ⟨m, f :: b :: d :: R, by omega, hm, hB, ⟨f, b, d, R, rfl, hwp⟩, ?_⟩
              simpa using h1
            · left
              have hbf : barB c0' f = false := by simpa using hb
              injection hstep with hstep; subst hstep
              exact biv_step c0' f b d R hB hfS hbf
          · exact absurd hstep (by simp)
        | [], _, hstep, _ => simp [step] at hstep
        | [_], _, hstep, _ => simp [step] at hstep
        | [_, _], _, hstep, _ => simp [step] at hstep
      · right
        refine ⟨m1, L1, by omega, hr1, hb1, hx1, ?_⟩
        have hadd2 := run_add (m - m1) 1 L1
        rw [hrest] at hadd2
        rw [show m + 1 - m1 = (m - m1) + 1 by omega, hadd2]
        simpa using h1

/-- the replayed handler e2 at the first c0'-prefixed front is y-free, the bare y, or (p'-headed).y -/
def trivH (e : T) : Prop := occ2 e = 0 ∨ e = var 2 ∨ ∃ s, e = app s (var 2) ∧ head s = var 0

theorem x1_handler (c0' f b d : T) (R : List T) (hw : head c0' = S) (hf : wpre c0' f)
    (hI : BIv c0' (f :: b :: d :: R)) :
    ∃ e1 e2 B', step (f :: b :: d :: R) = some (args c0' ++ e1 :: e2 :: B') ∧ trivH e2 := by
  have hfS : head f = S := by rw [wpre_headeq c0' f hf]; exact hw
  obtain ⟨us, hus⟩ := args_wpre c0' hw f hf
  obtain ⟨Tp, hL, hy, hn, ⟨e0, he0, hh0⟩⟩ := hI
  have hs : step (f :: b :: d :: R) = some (args c0' ++ (us ++ d :: app b d :: R)) := by
    simp [step, hfS, hus]
  -- f's arguments are y-free (f is in the y-free top part)
  have hfy : occ2 f = 0 := by
    match Tp, hL, hy with
    | [], hL, _ => simp [BOT] at hL; rw [hL.1] at hfS; simp [head] at hfS
    | t0 :: Tq, hL, hy => simp at hL; rw [hL.1]; exact hy t0 (by simp)
  have hus_y : ∀ u ∈ us, occ2 u = 0 := by
    intro u hu
    have hu' : u ∈ args f := by rw [hus]; simp [hu]
    exact occ2_args f hfy u hu'
  match us, hs, hus_y with
  | u1 :: u2 :: us', hs, hus_y =>
    exact ⟨u1, u2, us' ++ d :: app b d :: R, by simpa using hs, Or.inl (hus_y u2 (by simp))⟩
  | [u1], hs, _ =>
    refine ⟨u1, d, app b d :: R, by simpa using hs, ?_⟩
    -- d is in the top part (y-free) or is the bare y
    match Tp, hL, hy, hn with
    | [], _, _, hn => simp [nbar] at hn
    | [a1], _, _, hn => simp [nbar] at hn; split at hn <;> omega
    | [a1, b1], hL, _, _ => simp [BOT] at hL; right; left; exact hL.2.2.1
    | a1 :: b1 :: d1 :: R1, hL, hy, _ =>
      simp at hL; obtain ⟨_, _, hd, _⟩ := hL
      left; rw [hd]; exact hy d1 (by simp)
  | [], hs, _ =>
    refine ⟨d, app b d, R, by simpa using hs, ?_⟩
    match Tp, hL, hy, hn, he0 with
    | [], _, _, hn, _ => simp [nbar] at hn
    | [a1], _, _, hn, _ => simp [nbar] at hn; split at hn <;> omega
    | [a1, b1], hL, _, _, he0 =>
      simp [BOT] at hL
      obtain ⟨hf1, hb1, hd2, _⟩ := hL
      -- the p'-headed element of [f, b] is b (f is S-headed)
      simp at he0
      rcases he0 with he0 | he0
      · rw [he0, ← hf1, hfS] at hh0; simp at hh0
      · right; right; exact ⟨b, by rw [hd2], by rw [hb1, ← he0]; exact hh0⟩
    | a1 :: b1 :: d1 :: R1, hL, hy, _, _ =>
      simp at hL; obtain ⟨_, hb1, hd1, _⟩ := hL
      left; simp only [occ2]; rw [hb1, hd1]
      have := hy b1 (by simp); have := hy d1 (by simp); omega

/-- the Church-chain model's next datum: y -> p'' (= var 0), p' (= var 0) -> c' -/
def sbq (c' : Nat) : T → T
  | S => S
  | var n => if n = 0 then var c' else if n = 2 then var 0 else var n
  | app f x => app (sbq c' f) (sbq c' x)

def occ0 : T → Nat
  | S => 0
  | var n => if n = 0 then 1 else 0
  | app f x => occ0 f + occ0 x

theorem sbq_no_live (c' : Nat) (hc' : c' ≠ 0) : ∀ e : T, occ2 e = 0 → occ0 (sbq c' e) = 0
  | S, _ => by simp [sbq, occ0]
  | var n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [sbq, occ0, hc']
    · have h2 : n ≠ 2 := by intro e; subst e; simp [occ2] at h
      simp [sbq, occ0, h0, h2]
  | app f x, h => by
    simp only [occ2] at h
    simp only [sbq, occ0]
    rw [sbq_no_live c' hc' f (by omega), sbq_no_live c' hc' x (by omega)]

theorem sbq_head (c' : Nat) : ∀ s : T, head s = var 0 → head (sbq c' s) = var c'
  | S, h => by simp [head] at h
  | var n, h => by simp [head] at h; subst h; simp [sbq, head]
  | app f x, h => by simp only [sbq, head] at *; exact sbq_head c' f h

/-- the three kinds of replayed handler cannot start a further proper transfer in the Church-chain model:
    the next datum e2[y := p'', p' := c'] either does not contain the live atom at all, or is the bare p'' (whose
    run is stuck at once with the bare y at position 3), or is frozen-headed (stuck at once). -/
theorem trivH_next (c' : Nat) (hc' : c' ≠ 0) (e : T) (h : trivH e) :
    occ0 (sbq c' e) = 0 ∨ sbq c' e = var 0 ∨ ∃ s, sbq c' e = app s (var 0) ∧ head s = var c' := by
  rcases h with h | h | ⟨s, hs, hh⟩
  · left; exact sbq_no_live c' hc' e h
  · right; left; rw [h]; simp [sbq]
  · right; right
    refine ⟨sbq c' s, by rw [hs]; simp [sbq], ?_⟩
    exact sbq_head c' s hh

#print axioms x1_handler
#print axioms trivH_next
