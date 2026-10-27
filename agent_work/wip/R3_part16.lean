
/-! ### Theorem PAH: a single wrapper whose c-code is atom-headed (p- or frozen-headed) -/

/-- **THEOREM PAH.**  Single wrapper w = b0.c0 with b0 S-headed and y-free and c0 headed by an atom other than y
    (the live p, which becomes the frozen c, or a frozen atom).  Then every p'-headed front of the next phase has a
    y-free element or the bare y at position 3: the barrier phase can only end at a c0'-prefixed front, which is
    headed by a frozen atom and stuck (a re-execution). -/
theorem pah_main (b0 c0 : T) (c n : Nat) (hc2 : c ≠ 2) (hb0S : head b0 = S) (hy0 : occ2 b0 = 0)
    (hy1 : occ2 c0 = 0) (hn : head c0 = var n) (hn2 : n ≠ 2) :
    ∀ (m : Nat) (f b d : T) (R : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f :: b :: d :: R) →
      head f = var 0 → occ2 d = 0 ∨ d = var 2 := by
  intro m f b d R hm hf
  have hb0' : head (sb c b0) = S := sb_head c b0 hb0S
  have hy0' : occ2 (sb c b0) = 0 := sb_occ2 c hc2 b0 hy0
  have hy1' : occ2 (sb c c0) = 0 := sb_occ2 c hc2 c0 hy1
  have hc0'h : head (sb c c0) ≠ S := by
    have : sb c c0 = asub (fun k => if k = 0 then var c else var k) c0 := by
      clear hm hf hy1 hy1' hn hn2
      induction c0 with
      | S => simp [sb, asub]
      | var k => by_cases h : k = 0 <;> simp [sb, asub, h]
      | app f x ihf ihx => simp [sb, asub, ihf, ihx]
    rw [this, asub_headvar _ n c0 hn]
    by_cases h : n = 0 <;> simp [h, head]
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
      subst hL1
      have hf1 : head f1 ≠ S := by rw [wpre_headeq _ f1 hwp]; exact hc0'h
      have hj : m' - m1 = (m' - m1 - 1) + 1 := by omega
      rw [hj] at hrest
      simp only [run] at hrest
      rw [step_head_ne _ _ hf1] at hrest
      simp at hrest
