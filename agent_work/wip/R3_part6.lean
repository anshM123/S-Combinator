
/-! ### Theorem ALPHA: single-wrapper pattern alpha needs NO hypothesis beyond the glue step itself -/

theorem asub_args_var (sg : Nat → T) (n : Nat) (hS : head (sg n) = S) :
    ∀ f : T, head f = var n → args (asub sg f) = args (sg n) ++ (args f).map (asub sg)
  | S, h => by simp [head] at h
  | var m, h => by simp [head] at h; subst h; simp [asub, args]
  | app g x, h => by
    simp only [head] at h
    simp only [asub, args]
    rw [asub_args_var sg n hS g h]
    simp

theorem asub_sg3_sb (c : Nat) : ∀ t : T, occ2 t = 0 → asub (sg3 c) t = sb c t
  | S, _ => by simp [asub, sb]
  | var n, h => by
    by_cases h0 : n = 0
    · subst h0; simp [asub, sb, sg3]
    · have h2 : n ≠ 2 := by intro e; subst e; simp [occ2] at h
      simp [asub, sb, sg3, h0, h2]
  | app f x, h => by
    simp only [occ2] at h
    simp [asub, sb, asub_sg3_sb c f (by omega), asub_sg3_sb c x (by omega)]

/-- an image of an abstract run that is stuck (atom front, not p) or short before the time T' of a p-front list
    is impossible -/
theorem image_stuck (A : List T) (s2 : Nat → T) (B : List T) (L0 : List T) (t T' : Nat) (htT : t ≤ T')
    (ht : run t L0 = some (A.map (asub s2) ++ B)) (f b d : T) (R : List T)
    (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0)
    (j : Nat) (Aj : List T) (hj : run j A = some Aj) :
    (run (t + j + 1) L0 = none → (Aj.map (asub s2) ++ B) = f :: b :: d :: R ∧ t + j = T') ∧
    (T' < t + j → False) := by
  have p2 : ∀ i Ai, run i A = some Ai → run (t + i) L0 = some (Ai.map (asub s2) ++ B) := by
    intro i Ai hi
    rw [run_add t i, ht, Option.bind_some]
    exact run_append i _ _ B (asub_run s2 i _ _ hi)
  have early : T' < t + j → False := by
    intro hlt
    obtain ⟨Ai, hAi, _⟩ := run_prefix j (T' - t) A Aj hj (by omega)
    obtain ⟨g, rest, hg, hgS⟩ := run_front_S j (T' - t) A Aj Ai hj (by omega) hAi
    have h2 := p2 (T' - t) Ai hAi
    rw [show t + (T' - t) = T' by omega, hT, hg] at h2
    simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at h2
    have := asub_headS s2 g hgS
    rw [← h2.1, hf] at this; simp at this
  refine ⟨?_, early⟩
  intro hnone
  have hTle : T' ≤ t + j := by
    apply Nat.le_of_not_lt
    intro hlt
    have := run_none_after (t + j + 1) T' L0 hnone (by omega)
    rw [hT] at this; simp at this
  have hTe : T' = t + j := by
    apply Nat.le_antisymm hTle
    apply Nat.le_of_not_lt
    intro hlt; exact early hlt
  subst hTe
  have := p2 j Aj hj; rw [hT] at this; injection this with e
  exact ⟨e.symm, rfl⟩

/-- the hole substitution of pattern alpha: h1 -> y, h2 -> w.y -/
def sgA (h1 h2 : Nat) (wy : T) : Nat → T := fun n => if n = h1 then var 2 else if n = h2 then wy else var n

theorem asub_sgA_id (h1 h2 : Nat) (wy : T) : ∀ t : T, occN h1 t = 0 → occN h2 t = 0 → asub (sgA h1 h2 wy) t = t
  | S, _, _ => by simp [asub]
  | var n, ha, hb => by
    have n1 : n ≠ h1 := by intro e; subst e; simp [occN] at ha
    have n2 : n ≠ h2 := by intro e; subst e; simp [occN] at hb
    simp [asub, sgA, n1, n2]
  | app f x, ha, hb => by
    simp only [occN] at ha hb
    simp [asub, asub_sgA_id h1 h2 wy f (by omega) (by omega), asub_sgA_id h1 h2 wy x (by omega) (by omega)]

/-- **THEOREM ALPHA (pattern alpha, no replay hypothesis).**  Let the earlier phase (any run from L0) pass through
    the glue list [c0, w, y] ++ R0 with w = b0.c0 (b0, c0 S-headed, y-free) at time t and reach a p-front list with
    >= 3 elements at a later time T'.  Then the next phase of the handler w.y never makes a proper transfer: every
    p'-headed front has a y-free element or the bare y at position 3.  (Either c0's abstract run never calls its two
    arguments - Theorem PAF - or the earlier phase re-opens a copy of w.y - Theorem IGEN.) -/
theorem alpha_main (b0 c0 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H) (hb0S : head b0 = S) (hc0S : head c0 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hf1 : occN h1 c0 = 0) (hf2 : occN h2 c0 = 0) (hV : fresh3 H (app (app b0 c0) (var 2)))
    (L0 : List T) (t T' : Nat) (R0 : List T) (hglue : run t L0 = some (c0 :: app b0 c0 :: var 2 :: R0))
    (htT : t < T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  rcases Classical.em (∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g ≠ var h1 ∧ head g ≠ var h2) with hNH | hNH
  · exact paf_main b0 c0 c h1 h2 hc hc2 hh1 hh2 h12 hb0S hc0S hy0 hy1 hf1 hf2 hNH
  · -- some abstract front of c0's run is h1- or h2-headed
    have hex : ∃ k g L, run k (args c0 ++ [var h1, var h2]) = some (g :: L) ∧
        (head g = var h1 ∨ head g = var h2) := by
      apply Classical.byContradiction
      intro hno
      apply hNH
      intro k g L hk
      constructor
      · intro e; exact hno ⟨k, g, L, hk, Or.inl e⟩
      · intro e; exact hno ⟨k, g, L, hk, Or.inr e⟩
    obtain ⟨k, g, Lk, hk, hg⟩ := hex
    have hwyS : head (app (app b0 c0) (var 2)) = S := by simp [head, hb0S]
    have hs2_1 : sgA h1 h2 (app (app b0 c0) (var 2)) h1 = var 2 := by simp [sgA]
    have hs2_2 : sgA h1 h2 (app (app b0 c0) (var 2)) h2 = app (app b0 c0) (var 2) := by
      simp [sgA, Ne.symm h12]
    -- the earlier phase one step after the glue is the s2-image of the abstract list
    have hA2 : (args c0 ++ [var h1, var h2]).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0 =
        args c0 ++ var 2 :: app (app b0 c0) (var 2) :: R0 := by
      have hargs : (args c0).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) = args c0 := by
        have : (args c0).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) = (args c0).map id := by
          apply List.map_congr_left
          intro e he
          exact asub_sgA_id h1 h2 _ e (occN_args h1 c0 hf1 e he) (occN_args h2 c0 hf2 e he)
        simpa using this
      simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, hs2_1, hs2_2]
      simp
    have ht1 : run (t + 1) L0 = some ((args c0 ++ [var h1, var h2]).map
        (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0) := by
      rw [hA2, run_add t 1, hglue, Option.bind_some]
      simp [run, step, hc0S]
    obtain ⟨hstuckE, hearly⟩ := image_stuck _ _ R0 L0 (t + 1) T' (by omega) ht1 f b d R hT hf k (g :: Lk) hk
    have p2k : run (t + 1 + k) L0 =
        some ((g :: Lk).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0) := by
      rw [run_add (t + 1) k, ht1, Option.bind_some]
      exact run_append k _ _ R0 (asub_run _ k _ _ hk)
    rcases hg with hg | hg
    · -- an h1-front would be a y-front of the earlier phase: impossible
      exfalso
      have hy : head (asub (sgA h1 h2 (app (app b0 c0) (var 2))) g) = var 2 := by
        rw [asub_headvar _ h1 g hg, hs2_1]; simp [head]
      have hnone : run (t + 1 + k + 1) L0 = none := by
        rw [run_add (t + 1 + k) 1, p2k, Option.bind_some]
        simp only [run, List.map_cons, List.cons_append]
        rw [step_head_ne _ _ (by rw [hy]; simp)]
      obtain ⟨he, _⟩ := hstuckE hnone
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
      rw [← he.1, hy] at hf; injection hf with e; omega
    · -- an h2-front: the earlier phase opens a copy of w.y, i.e. lays out args(w.y): Theorem IGEN
      have hGS : head (asub (sgA h1 h2 (app (app b0 c0) (var 2))) g) = S := by
        rw [asub_headvar _ h2 g hg, hs2_2]; exact hwyS
      -- the earlier phase makes a step at time t + 1 + k
      have hTgt : t + 1 + k < T' := by
        apply Nat.lt_of_not_le
        intro hle
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact hearly (by omega)
        · subst heq
          rw [p2k] at hT
          simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at hT
          rw [← hT.1, hGS] at hf; simp at hf
      obtain ⟨Ln, hLn, _⟩ := run_prefix T' (t + 1 + k + 1) L0 _ hT (by omega)
      have hstep : step ((g :: Lk).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0) = some Ln := by
        rw [run_add (t + 1 + k) 1, p2k, Option.bind_some] at hLn
        simp only [run] at hLn
        cases hs : step ((g :: Lk).map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0) with
        | none => rw [hs] at hLn; simp at hLn
        | some L1 => rw [hs] at hLn; simpa using hLn
      -- Ln starts with args(w.y)
      have hargsG := asub_args_var (sgA h1 h2 (app (app b0 c0) (var 2))) h2 (by rw [hs2_2]; exact hwyS) g hg
      rw [hs2_2] at hargsG
      have hLn_form : ∃ B2, Ln = args (app (app b0 c0) (var 2)) ++ B2 := by
        simp only [List.map_cons, List.cons_append] at hstep
        match hrest : Lk.map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) ++ R0, hstep with
        | b2 :: d2 :: R2, hstep =>
          simp only [step, hGS, ite_true, Option.some.injEq] at hstep
          rw [hargsG] at hstep
          exact ⟨List.map (asub (sgA h1 h2 (app (app b0 c0) (var 2)))) (args g) ++ d2 :: app b2 d2 :: R2,
            by rw [← hstep, List.append_assoc]⟩
        | [], hstep => simp [step] at hstep
        | [_], hstep => simp [step] at hstep
      obtain ⟨B2, hB2⟩ := hLn_form
      rw [hB2] at hLn
      have hVa : args (app (app b0 c0) (var 2)) ≠ [] := by simp [args]
      have hno := igen_main (app (app b0 c0) (var 2)) c H hc hH hwyS hVa hV L0 (t + 1 + k + 1) T' B2
        (by omega) hLn f b d R hT hf
      have hD3 : asub (sg3 c) (app (app b0 c0) (var 2)) = app (app (sb c b0) (sb c c0)) (var 0) := by
        simp [asub, asub_sg3_sb c b0 hy0, asub_sg3_sb c c0 hy1, sg3]
      intro m f' b' d' R' hm hf'
      rw [← hD3] at hm
      exact absurd hf' (hno m f' _ hm)
