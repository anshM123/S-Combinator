
/-! ### Theorem CLOSEDGLUE: a glue [a1, w, y] whose front a1 does not contain the live atom forces IGEN -/

theorem occN_run (n : Nat) : ∀ (k : Nat) (L L' : List T), (∀ e ∈ L, occN n e = 0) → run k L = some L' →
    ∀ e ∈ L', occN n e = 0
  | 0, L, L', h0, h => by simp [run] at h; subst h; exact h0
  | k + 1, L, L', h0, h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      simp only at h
      apply occN_run n k L1 L' _ h
      match L, hs, h0 with
      | a :: b :: d :: R, hs, h0 =>
        simp only [step] at hs
        split at hs
        · injection hs with hs; subst hs
          intro e he; simp at he
          rcases he with he | he | he | he
          · exact occN_args n a (h0 a (by simp)) e he
          · rw [he]; exact h0 d (by simp)
          · rw [he]; simp only [occN]; have := h0 b (by simp); have := h0 d (by simp); omega
          · exact h0 e (by simp [he])
        · simp at hs
      | [], hs, _ => simp [step] at hs
      | [_], hs, _ => simp [step] at hs
      | [_, _], hs, _ => simp [step] at hs

theorem occN_head (n : Nat) : ∀ t : T, head t = var n → occN n t ≠ 0
  | S, h => by simp [head] at h
  | var m, h => by simp [head] at h; subst h; simp [occN]
  | app f x, h => by
    simp only [head] at h
    have := occN_head n f h
    simp only [occN]; omega

/-- **THEOREM CLOSEDGLUE.**  If the earlier phase (any run from L0) passes through a glue list [a1, w, y] ++ R0 whose
    front a1 is S-headed and free of the live atom p (var 0) (frozen atoms allowed), and later reaches a p-front list
    with >= 3 elements, then the next phase of w.y (w S-headed) has NO p'-front at all.  (Run from the glue, a1's
    code cannot bring p to the front; calling its first hole is a y-call of the earlier phase; so it calls its second
    hole w.y, i.e. the earlier phase opens a copy of w.y and lays out args(w.y): IGEN.) -/
theorem closedglue_main (a1 w : T) (c h1 h2 H : Nat) (hc : c ≠ 0) (hh1 : h1 ≠ 0) (hh2 : h2 ≠ 0)
    (h12 : h1 ≠ h2) (hH : 4 ≤ H) (ha1S : head a1 = S) (ha10 : occN 0 a1 = 0) (hwS : head w = S)
    (hf1 : occN h1 a1 = 0) (hf2 : occN h2 a1 = 0) (hV : fresh3 H (app w (var 2)))
    (L0 : List T) (t T' : Nat) (R0 : List T) (hglue : run t L0 = some (a1 :: w :: var 2 :: R0))
    (htT : t < T') (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' : T) (L' : List T),
      run m [asub (sg3 c) (app w (var 2)), var 1, var 2, var 3] = some (f' :: L') → head f' ≠ var 0 := by
  have hwyS : head (app w (var 2)) = S := by simp [head, hwS]
  have hs2_1 : sgA h1 h2 (app w (var 2)) h1 = var 2 := by simp [sgA]
  have hs2_2 : sgA h1 h2 (app w (var 2)) h2 = app w (var 2) := by simp [sgA, Ne.symm h12]
  have hA2 : (args a1 ++ [var h1, var h2]).map (asub (sgA h1 h2 (app w (var 2)))) ++ R0 =
      args a1 ++ var 2 :: app w (var 2) :: R0 := by
    have hargs : (args a1).map (asub (sgA h1 h2 (app w (var 2)))) = args a1 := by
      have : (args a1).map (asub (sgA h1 h2 (app w (var 2)))) = (args a1).map id := by
        apply List.map_congr_left
        intro e he
        exact asub_sgA_id h1 h2 _ e (occN_args h1 a1 hf1 e he) (occN_args h2 a1 hf2 e he)
      simpa using this
    simp only [List.map_append, hargs, List.map_cons, List.map_nil, asub, hs2_1, hs2_2]
    simp
  have ht1 : run (t + 1) L0 = some ((args a1 ++ [var h1, var h2]).map
      (asub (sgA h1 h2 (app w (var 2)))) ++ R0) := by
    rw [hA2, run_add t 1, hglue, Option.bind_some]
    simp [run, step, ha1S]
  have hA0 : ∀ e ∈ args a1 ++ [var h1, var h2], occN 0 e = 0 := by
    intro e he; simp at he
    rcases he with he | he | he
    · exact occN_args 0 a1 ha10 e he
    · rw [he]; simp [occN]; omega
    · rw [he]; simp [occN]; omega
  have hnB : 2 ≤ nHB h1 h2 (args a1 ++ [var h1, var h2]) := by
    rw [nHB_append]; simp [nHB, isHB, head]
  -- the image of an abstract front that is not h2-headed is never a var 0-headed or S-headed-then-p front
  have himg : ∀ g : T, head g ≠ var h2 → occN 0 g = 0 →
      head (asub (sgA h1 h2 (app w (var 2))) g) ≠ var 0 := by
    intro g hg2 hg0
    rcases head_cases g with hgS | ⟨n, hn⟩
    · rw [asub_headS _ g hgS]; simp
    · rw [asub_headvar _ n g hn]
      have hn0 : n ≠ 0 := by intro e; subst e; exact occN_head 0 g hn hg0
      have hn2 : n ≠ h2 := by intro e; subst e; exact hg2 hn
      by_cases e1 : n = h1
      · subst e1; rw [hs2_1]; simp [head]
      · simp [sgA, e1, hn2, head, hn0]
  have hex : ∃ k g Lk, run k (args a1 ++ [var h1, var h2]) = some (g :: Lk) ∧ head g = var h2 := by
    apply Classical.byContradiction
    intro hno
    cases hj : run (T' - (t + 1)) (args a1 ++ [var h1, var h2]) with
    | some AT =>
      -- the earlier phase at time T' is the image of AT
      have h2T : run T' L0 = some (AT.map (asub (sgA h1 h2 (app w (var 2)))) ++ R0) := by
        rw [show T' = (t + 1) + (T' - (t + 1)) by omega, run_add (t + 1) (T' - (t + 1)), ht1, Option.bind_some]
        exact run_append _ _ _ R0 (asub_run _ _ _ _ hj)
      rw [hT] at h2T
      have hne := run_ne_nil _ _ AT (by simp) hj
      match AT, hne, h2T, hj with
      | g :: Lg, _, h2T, hj =>
        simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at h2T
        have hg2 : head g ≠ var h2 := fun e => hno ⟨_, g, Lg, hj, e⟩
        have hg0 : occN 0 g = 0 := occN_run 0 _ _ _ hA0 hj g (by simp)
        exact himg g hg2 hg0 (by rw [← h2T.1]; exact hf)
    | none =>
      obtain ⟨k, Ak, hk, hrk, hsk⟩ := run_first_none _ _ hj
      obtain ⟨g, rest, hAk, hgS⟩ := nHB_stop h1 h2 _ Ak k hnB hrk hsk
      subst hAk
      obtain ⟨hstuckE, _⟩ := image_stuck _ _ R0 L0 (t + 1) T' (by omega) ht1 f b d R hT hf k _ hrk
      have hg2 : head g ≠ var h2 := fun e => hno ⟨k, g, rest, hrk, e⟩
      have hg0 : occN 0 g = 0 := occN_run 0 _ _ _ hA0 hrk g (by simp)
      have hneS : head (asub (sgA h1 h2 (app w (var 2))) g) ≠ S := by
        obtain ⟨n, hn⟩ : ∃ n, head g = var n := (head_cases g).resolve_left hgS
        rw [asub_headvar _ n g hn]
        have hn2 : n ≠ h2 := by intro e; subst e; exact hg2 hn
        by_cases e1 : n = h1
        · subst e1; rw [hs2_1]; simp [head]
        · simp [sgA, e1, hn2, head]
      have hp2 : run (t + 1 + k) L0 = some ((g :: rest).map (asub (sgA h1 h2 (app w (var 2)))) ++ R0) := by
        rw [run_add (t + 1) k, ht1, Option.bind_some]
        exact run_append k _ _ R0 (asub_run _ k _ _ hrk)
      have hnone : run (t + 1 + k + 1) L0 = none := by
        rw [run_add (t + 1 + k) 1, hp2, Option.bind_some]
        simp only [run, List.map_cons, List.cons_append]
        rw [step_head_ne _ _ hneS]
      obtain ⟨he, _⟩ := hstuckE hnone
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
      exact himg g hg2 hg0 (by rw [he.1]; exact hf)
  -- an h2-front: the earlier phase opens a copy of w.y, IGEN
  obtain ⟨k, g, Lk, hk, hg⟩ := hex
  obtain ⟨_, hearly⟩ := image_stuck _ _ R0 L0 (t + 1) T' (by omega) ht1 f b d R hT hf k (g :: Lk) hk
  have p2k : run (t + 1 + k) L0 = some ((g :: Lk).map (asub (sgA h1 h2 (app w (var 2)))) ++ R0) := by
    rw [run_add (t + 1) k, ht1, Option.bind_some]
    exact run_append k _ _ R0 (asub_run _ k _ _ hk)
  have hGS : head (asub (sgA h1 h2 (app w (var 2))) g) = S := by
    rw [asub_headvar _ h2 g hg, hs2_2]; exact hwyS
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
  have hstep : step ((g :: Lk).map (asub (sgA h1 h2 (app w (var 2)))) ++ R0) = some Ln := by
    rw [run_add (t + 1 + k) 1, p2k, Option.bind_some] at hLn
    simp only [run] at hLn
    cases hs : step ((g :: Lk).map (asub (sgA h1 h2 (app w (var 2)))) ++ R0) with
    | none => rw [hs] at hLn; simp at hLn
    | some L1 => rw [hs] at hLn; simpa using hLn
  have hargsG := asub_args_var (sgA h1 h2 (app w (var 2))) h2 (by rw [hs2_2]; exact hwyS) g hg
  rw [hs2_2] at hargsG
  have hLn_form : ∃ B2, Ln = args (app w (var 2)) ++ B2 := by
    simp only [List.map_cons, List.cons_append] at hstep
    match hrest : Lk.map (asub (sgA h1 h2 (app w (var 2)))) ++ R0, hstep with
    | b2 :: d2 :: R2, hstep =>
      simp only [step, hGS, ite_true, Option.some.injEq] at hstep
      rw [hargsG] at hstep
      exact ⟨List.map (asub (sgA h1 h2 (app w (var 2)))) (args g) ++ d2 :: app b2 d2 :: R2,
        by rw [← hstep, List.append_assoc]⟩
    | [], hstep => simp [step] at hstep
    | [_], hstep => simp [step] at hstep
  obtain ⟨B2, hB2⟩ := hLn_form
  rw [hB2] at hLn
  have hVa : args (app w (var 2)) ≠ [] := by simp [args]
  exact igen_main (app w (var 2)) c H hc hH hwyS hVa hV L0 (t + 1 + k + 1) T' B2 (by omega) hLn f b d R hT hf
