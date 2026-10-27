
/-! ### Theorem BETA0: pattern beta reduced to 'phase 2 runs c0 on (w, y)' plus a residual condition on c0 alone -/

/-- the hole substitution of BETA0: h1 -> w, h2 -> y -/
def sgB (h1 h2 : Nat) (w : T) : Nat → T := fun n => if n = h1 then w else if n = h2 then var 2 else var n

theorem asub_sgB_id (h1 h2 : Nat) (w : T) : ∀ t : T, occN h1 t = 0 → occN h2 t = 0 → asub (sgB h1 h2 w) t = t
  | S, _, _ => by simp [asub]
  | var n, ha, hb => by
    have n1 : n ≠ h1 := by intro e; subst e; simp [occN] at ha
    have n2 : n ≠ h2 := by intro e; subst e; simp [occN] at hb
    simp [asub, sgB, n1, n2]
  | app f x, ha, hb => by
    simp only [occN] at ha hb
    simp [asub, asub_sgB_id h1 h2 w f (by omega) (by omega), asub_sgB_id h1 h2 w x (by omega) (by omega)]

/-- **THEOREM BETA0.**  Single wrapper w = b0.c0.  Let the earlier phase (any run from L0) run c0 on the holes
    (w, y), i.e. reach args(c0) ++ [w, y] ++ B2 at time t, and reach a p-front list with >= 3 elements at T' > t.
    Assume the residual condition H1ok on c0 alone: whenever the abstract run of args(c0) ++ [h1, h2] reaches an
    h1-headed front, that front is h1.h2.(...) or the bare h1 with h2 at position 3.  Then the next phase of w.y never
    makes a proper transfer.  (Cases: c0 never calls its holes - PAF; it calls h2 - a y-front of the earlier phase,
    impossible; it calls h1 - the earlier phase opens w with y as first argument, i.e. lays out args(w.y) - IGEN.) -/
theorem beta_main (b0 c0 : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hc2 : c ≠ 2) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H) (hb0S : head b0 = S) (hc0S : head c0 = S) (hy0 : occ2 b0 = 0) (hy1 : occ2 c0 = 0)
    (hf1 : occN h1 c0 = 0) (hf2 : occN h2 c0 = 0) (hV : fresh3 H (app (app b0 c0) (var 2)))
    (L0 : List T) (t T' : Nat) (B2 : List T)
    (hc0w : run t L0 = some (args c0 ++ app b0 c0 :: var 2 :: B2))
    (htT : t < T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0)
    (hH1 : ∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g = var h1 → (args g).head? = some (var h2) ∨ (args g = [] ∧ ∃ b' R', L = b' :: var h2 :: R')) :
    ∀ (m : Nat) (f' b' d' : T) (R' : List T),
      run m [app (app (sb c b0) (sb c c0)) (var 0), var 1, var 2, var 3] = some (f' :: b' :: d' :: R') →
      head f' = var 0 → occ2 d' = 0 ∨ d' = var 2 := by
  rcases Classical.em (∀ (k : Nat) (g : T) (L : List T), run k (args c0 ++ [var h1, var h2]) = some (g :: L) →
      head g ≠ var h1 ∧ head g ≠ var h2) with hNH | hNH
  · exact paf_main b0 c0 c h1 h2 hc hc2 hh1 hh2 h12 hb0S hc0S hy0 hy1 hf1 hf2 hNH
  · have hex : ∃ k g L, run k (args c0 ++ [var h1, var h2]) = some (g :: L) ∧
        (head g = var h1 ∨ head g = var h2) := by
      apply Classical.byContradiction
      intro hno
      apply hNH
      intro k g L hk
      constructor
      · intro e; exact hno ⟨k, g, L, hk, Or.inl e⟩
      · intro e; exact hno ⟨k, g, L, hk, Or.inr e⟩
    obtain ⟨k, g, Lk, hk, hg⟩ := hex
    have hwS : head (app b0 c0) = S := by simp [head, hb0S]
    have hwyS : head (app (app b0 c0) (var 2)) = S := by simp [head, hb0S]
    have hs1 : sgB h1 h2 (app b0 c0) h1 = app b0 c0 := by simp [sgB]
    have hs2 : sgB h1 h2 (app b0 c0) h2 = var 2 := by simp [sgB, Ne.symm h12]
    have hA2 : (args c0 ++ [var h1, var h2]).map (asub (sgB h1 h2 (app b0 c0))) ++ B2 =
        args c0 ++ app b0 c0 :: var 2 :: B2 := by
      have hargs : (args c0).map (asub (sgB h1 h2 (app b0 c0))) = args c0 := by
        have : (args c0).map (asub (sgB h1 h2 (app b0 c0))) = (args c0).map id := by
          apply List.map_congr_left
          intro e he
          exact asub_sgB_id h1 h2 _ e (occN_args h1 c0 hf1 e he) (occN_args h2 c0 hf2 e he)
        simpa using this
      simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, hs1, hs2]
      simp
    have ht' : run t L0 = some ((args c0 ++ [var h1, var h2]).map (asub (sgB h1 h2 (app b0 c0))) ++ B2) := by
      rw [hA2]; exact hc0w
    obtain ⟨hstuckE, hearly⟩ := image_stuck _ _ B2 L0 t T' (by omega) ht' f b d R hT hf k (g :: Lk) hk
    have p2k : run (t + k) L0 = some ((g :: Lk).map (asub (sgB h1 h2 (app b0 c0))) ++ B2) := by
      rw [run_add t k, ht', Option.bind_some]
      exact run_append k _ _ B2 (asub_run _ k _ _ hk)
    rcases hg with hg | hg
    · -- h1-front: the earlier phase opens w; by H1ok its first argument is y: IGEN
      have hGS : head (asub (sgB h1 h2 (app b0 c0)) g) = S := by
        rw [asub_headvar _ h1 g hg, hs1]; exact hwS
      have hTgt : t + k < T' := by
        apply Nat.lt_of_not_le
        intro hle
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact hearly (by omega)
        · subst heq
          rw [p2k] at hT
          simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at hT
          rw [← hT.1, hGS] at hf; simp at hf
      obtain ⟨Ln, hLn, _⟩ := run_prefix T' (t + k + 1) L0 _ hT (by omega)
      have hstep : step ((g :: Lk).map (asub (sgB h1 h2 (app b0 c0))) ++ B2) = some Ln := by
        rw [run_add (t + k) 1, p2k, Option.bind_some] at hLn
        simp only [run] at hLn
        cases hs : step ((g :: Lk).map (asub (sgB h1 h2 (app b0 c0))) ++ B2) with
        | none => rw [hs] at hLn; simp at hLn
        | some L1 => rw [hs] at hLn; simpa using hLn
      have hargsG := asub_args_var (sgB h1 h2 (app b0 c0)) h1 (by rw [hs1]; exact hwS) g hg
      rw [hs1] at hargsG
      have hLn_form : ∃ B3, Ln = args (app (app b0 c0) (var 2)) ++ B3 := by
        have hwy_args : args (app (app b0 c0) (var 2)) = args (app b0 c0) ++ [var 2] := by simp [args]
        rcases hH1 k g Lk hk hg with hfirst | ⟨hnil, b'', R'', hL⟩
        · -- the front is w.y.(...)
          match hag : args g, hfirst with
          | u :: us, hfirst =>
            simp only [List.head?, Option.some.injEq] at hfirst
            subst hfirst
            rw [hag] at hargsG
            simp only [List.map_cons, List.cons_append] at hstep
            match hrest : Lk.map (asub (sgB h1 h2 (app b0 c0))) ++ B2, hstep with
            | b2 :: d2 :: R2, hstep =>
              simp only [step, hGS, ite_true, Option.some.injEq] at hstep
              rw [hargsG] at hstep
              refine ⟨List.map (asub (sgB h1 h2 (app b0 c0))) us ++ d2 :: app b2 d2 :: R2, ?_⟩
              rw [← hstep, hwy_args]
              simp [asub, hs2]
            | [], hstep => simp [step] at hstep
            | [_], hstep => simp [step] at hstep
        · -- the front is the bare h1 (so its image is w) with h2 (image y) at position 3
          subst hL
          rw [hnil] at hargsG
          simp only [List.map_cons, List.cons_append, List.map_nil] at hstep
          simp only [step, hGS, ite_true, Option.some.injEq] at hstep
          rw [hargsG] at hstep
          refine ⟨app (asub (sgB h1 h2 (app b0 c0)) b'') (var 2) ::
            (List.map (asub (sgB h1 h2 (app b0 c0))) R'' ++ B2), ?_⟩
          rw [← hstep, hwy_args]
          simp [asub, hs2]
      obtain ⟨B3, hB3⟩ := hLn_form
      rw [hB3] at hLn
      have hVa : args (app (app b0 c0) (var 2)) ≠ [] := by simp [args]
      have hno := igen_main (app (app b0 c0) (var 2)) c H hc hH hwyS hVa hV L0 (t + k + 1) T' B3
        (by omega) hLn f b d R hT hf
      have hD3 : asub (sg3 c) (app (app b0 c0) (var 2)) = app (app (sb c b0) (sb c c0)) (var 0) := by
        simp [asub, asub_sg3_sb c b0 hy0, asub_sg3_sb c c0 hy1, sg3]
      intro m f' b' d' R' hm hf'
      rw [← hD3] at hm
      exact absurd hf' (hno m f' _ hm)
    · -- h2-front: a y-front of the earlier phase, impossible
      exfalso
      have hy : head (asub (sgB h1 h2 (app b0 c0)) g) = var 2 := by
        rw [asub_headvar _ h2 g hg, hs2]; simp [head]
      have hnone : run (t + k + 1) L0 = none := by
        rw [run_add (t + k) 1, p2k, Option.bind_some]
        simp only [run, List.map_cons, List.cons_append]
        rw [step_head_ne _ _ (by rw [hy]; simp)]
      obtain ⟨he, _⟩ := hstuckE hnone
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
      rw [← he.1, hy] at hf; injection hf with e; omega
