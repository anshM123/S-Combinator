
/-! ### Theorem NHALL: multi-wrapper handlers whose every level's c-code never calls its holes -/

/-- generic barrier count -/
def nbarG (bar : T → Bool) : List T → Nat
  | [] => 0
  | e :: L => (if bar e = true then 1 else 0) + nbarG bar L

theorem nbarG_append (bar : T → Bool) : ∀ A B : List T, nbarG bar (A ++ B) = nbarG bar A + nbarG bar B
  | [], B => by simp [nbarG]
  | e :: A, B => by simp [nbarG, nbarG_append bar A B]; omega

def BIG (bar : T → Bool) (B : List T) (L : List T) : Prop :=
  ∃ Tp : List T, L = Tp ++ B ∧ (∀ e ∈ Tp, occ2 e = 0) ∧ 2 ≤ nbarG bar Tp

theorem big2_shape (bar : T → Bool) (B : List T) (a : T) (L : List T) (hI : BIG bar B (a :: L))
    (hna : bar a = false) :
    ∃ b d R', a :: L = a :: b :: d :: R' ++ B ∧ (∀ e ∈ a :: b :: d :: R', occ2 e = 0) ∧
      2 ≤ nbarG bar (b :: d :: R') := by
  obtain ⟨Tp, hL, hy, hn⟩ := hI
  match Tp, hL, hy, hn with
  | [], _, _, hn => simp [nbarG] at hn
  | [a1], _, _, hn => simp [nbarG] at hn; split at hn <;> omega
  | [a1, b1], hL, _, hn =>
    simp at hL; obtain ⟨rfl, _⟩ := hL
    simp [nbarG, hna] at hn; split at hn <;> omega
  | a1 :: b1 :: d1 :: R1, hL, hy, hn =>
    simp at hL; obtain ⟨rfl, hL2⟩ := hL
    refine ⟨b1, d1, R1, by rw [hL2]; simp, hy, ?_⟩
    simp [nbarG, hna] at hn ⊢; omega

theorem big2_step (bar : T → Bool) (hbar : ∀ b d, bar b = true → bar (app b d) = true)
    (B : List T) (a b d : T) (R : List T) (hI : BIG bar B (a :: b :: d :: R))
    (hna : bar a = false) : BIG bar B (args a ++ d :: app b d :: R) := by
  obtain ⟨b1, d1, R1, hL, hy, hn⟩ := big2_shape bar B a _ hI hna
  simp at hL
  obtain ⟨rfl, rfl, hR⟩ := hL
  refine ⟨args a ++ d :: app b d :: R1, by rw [hR]; simp, ?_, ?_⟩
  · intro e he; simp at he
    rcases he with he | he | he | he
    · exact occ2_args a (hy a (by simp)) e he
    · rw [he]; exact hy d (by simp)
    · rw [he]; simp only [occ2]; have := hy b (by simp); have := hy d (by simp); omega
    · exact hy e (by simp [he])
  · rw [nbarG_append]
    have hbd : (if bar b = true then 1 else 0) ≤ (if bar (app b d) = true then 1 else 0) := by
      by_cases hb : bar b = true
      · simp [hb, hbar b d hb]
      · simp [hb]
    simp only [nbarG] at hn ⊢
    omega

/-- at a barrier front of a BIG list, position 3 is a y-free top element or the first bottom element -/
theorem big2_pos3 (bar : T → Bool) (B : List T) (hB : B0ok B) (a b d : T) (R : List T)
    (hI : BIG bar B (a :: b :: d :: R)) : occ2 d = 0 ∨ d = var 2 := by
  obtain ⟨Tp, hL, hy, hn⟩ := hI
  match Tp, hL, hy, hn with
  | [], _, _, hn => simp [nbarG] at hn
  | [a1], _, _, hn => simp [nbarG] at hn; split at hn <;> omega
  | [a1, b1], hL, _, _ =>
    simp at hL
    obtain ⟨_, _, hB2⟩ := hL
    exact hB d (by rw [← hB2]; simp)
  | a1 :: b1 :: d1 :: R1, hL, hy, _ =>
    simp at hL; obtain ⟨_, _, rfl, _⟩ := hL
    left; exact hy d (by simp)

/-- the first barrier front of a BIG phase -/
theorem big2_phase (bar : T → Bool) (hbar : ∀ b d, bar b = true → bar (app b d) = true) (B : List T)
    (L0 : List T) (h0 : BIG bar B L0) :
    ∀ (m : Nat) (L : List T), run m L0 = some L →
    BIG bar B L ∨ ∃ m1 L1, m1 < m ∧ run m1 L0 = some L1 ∧ BIG bar B L1 ∧
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
      rcases big2_phase bar hbar B L0 h0 m Lm hm with hB | ⟨m1, L1, hlt, hr1, hb1, hx1, hrest⟩
      · match Lm, hB, hstep, hm with
        | f :: b :: d :: R, hB, hstep, hm =>
          by_cases hb : bar f = true
          · right
            exact ⟨m, f :: b :: d :: R, by omega, hm, hB, ⟨f, b, d, R, rfl, hb⟩, by simpa using h1⟩
          · left
            simp only [step] at hstep
            split at hstep
            · injection hstep with hstep; subst hstep
              exact big2_step bar hbar B f b d R hB (by simpa using hb)
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
