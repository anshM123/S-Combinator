
/-! ### The general correspondence lemma (GCL): two images of one abstract run -/

theorem run_ne_nil : ∀ (k : Nat) (L L' : List T), L ≠ [] → run k L = some L' → L' ≠ []
  | 0, L, L', hL, h => by simp [run] at h; subst h; exact hL
  | k + 1, L, L', hL, h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      simp only at h
      apply run_ne_nil k L1 L' _ h
      match L, hs with
      | a :: b :: d :: R, hs =>
        simp only [step] at hs
        split at hs
        · injection hs with hs; subst hs; simp
        · simp at hs
      | [], hs => simp [step] at hs
      | [_], hs => simp [step] at hs
      | [_, _], hs => simp [step] at hs

/-- every front strictly before the end of a successful run is S-headed -/
theorem run_front_S (k j : Nat) (L L' Lj : List T) (h : run k L = some L') (hj : j < k)
    (hLj : run j L = some Lj) : ∃ g rest, Lj = g :: rest ∧ head g = S := by
  obtain ⟨Lj', hLj', hrest⟩ := run_prefix k j L L' h (by omega)
  rw [hLj] at hLj'; injection hLj' with e; subst e
  have hk : k - j = (k - j - 1) + 1 := by omega
  rw [hk] at hrest
  simp only [run] at hrest
  cases hs : step Lj with
  | none => rw [hs] at hrest; simp at hrest
  | some L1 =>
    match Lj, hs with
    | a :: b :: d :: R, hs =>
      refine ⟨a, b :: d :: R, rfl, ?_⟩
      simp only [step] at hs
      split at hs
      · assumption
      · simp at hs
    | [], hs => simp [step] at hs
    | [_], hs => simp [step] at hs
    | [_, _], hs => simp [step] at hs

/-- **GCL.**  One abstract list A, two atom substitutions: s2 (the earlier phase, which later reaches a p-front
    with at least three elements) and s3 (the next phase), with one of the two bottoms empty.  If s3 maps every
    atom to an atom-headed term and maps to a p'-headed term (var 0) only atoms that s2 maps to a term headed by a
    DIFFERENT atom, then the s3-run never reaches a var 0-headed front. -/
theorem gcl (A : List T) (hA0 : A ≠ []) (s2 s3 : Nat → T) (B2r B3r : List T) (hB : B2r = [] ∨ B3r = [])
    (C1 : ∀ n, head (s3 n) ≠ S)
    (C2 : ∀ n, head (s3 n) = var 0 → ∃ m, head (s2 n) = var m ∧ m ≠ 0)
    (L0 : List T) (t T' : Nat) (htT : t ≤ T') (ht : run t L0 = some (A.map (asub s2) ++ B2r))
    (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' : T) (L' : List T), run m (A.map (asub s3) ++ B3r) = some (f' :: L') → head f' ≠ var 0 := by
  intro m f' L' h3 hf'
  -- phase-2 facts at time t + j
  have p2 : ∀ j Aj, run j A = some Aj → run (t + j) L0 = some (Aj.map (asub s2) ++ B2r) := by
    intro j Aj hj
    rw [run_add t j, ht, Option.bind_some]
    exact run_append j _ _ B2r (asub_run s2 j _ _ hj)
  -- if phase 2 is stuck (or short) at time t + j while the abstract run reached step j, then t + j = T'
  have p2stuck : ∀ j Aj, run j A = some Aj → run (t + j + 1) L0 = none →
      t + j = T' ∧ (Aj.map (asub s2) ++ B2r) = f :: b :: d :: R := by
    intro j Aj hj hnone
    have hTle : T' ≤ t + j := by
      apply Nat.le_of_not_lt
      intro hlt
      have := run_none_after (t + j + 1) T' L0 hnone (by omega)
      rw [hT] at this; simp at this
    by_cases hTe : T' = t + j
    · subst hTe; refine ⟨rfl, ?_⟩
      have := p2 j Aj hj; rw [hT] at this; injection this with e; exact e.symm
    · exfalso
      have hlt : T' - t < j := by omega
      obtain ⟨Aj', hAj'⟩ : ∃ Aj', run (T' - t) A = some Aj' := by
        obtain ⟨Lx, hLx, _⟩ := run_prefix j (T' - t) A Aj hj (by omega)
        exact ⟨Lx, hLx⟩
      obtain ⟨g, rest, hg, hgS⟩ := run_front_S j (T' - t) A Aj Aj' hj hlt hAj'
      have h2 := p2 (T' - t) Aj' hAj'
      rw [show t + (T' - t) = T' by omega, hT, hg] at h2
      simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at h2
      have := asub_headS s2 g hgS
      rw [← h2.1, hf] at this; simp at this
  cases hm : run m A with
  | some Am =>
    have h3' := run_append m _ _ B3r (asub_run s3 m _ _ hm)
    rw [h3] at h3'
    have hne := run_ne_nil m A Am hA0 hm
    match Am, hm, h3', hne with
    | [], _, _, hne => exact hne rfl
    | f0 :: L0', hm, h3', _ =>
      simp only [List.map_cons, List.cons_append, Option.some.injEq, List.cons.injEq] at h3'
      obtain ⟨hff, _⟩ := h3'
      rcases head_cases f0 with hS | ⟨n, hn⟩
      · have := asub_headS s3 f0 hS
        rw [← hff, hf'] at this; simp at this
      · have hh := asub_headvar s3 n f0 hn
        rw [← hff, hf'] at hh
        obtain ⟨m', hm', hm0⟩ := C2 n hh.symm
        -- phase 2 is stuck at time t + m with front headed by var m'
        have h2 := p2 m _ hm
        have hstuck : run (t + m + 1) L0 = none := by
          rw [run_add (t + m) 1, h2, Option.bind_some]
          simp only [run, List.map_cons, List.cons_append]
          rw [step_head_ne _ _ (by rw [asub_headvar s2 n f0 hn, hm']; simp)]
        obtain ⟨_, he⟩ := p2stuck m _ hm hstuck
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at he
        have := asub_headvar s2 n f0 hn
        rw [he.1, hf, hm'] at this
        injection this with e; exact hm0 e.symm
  | none =>
    obtain ⟨k, Ak, hk, hrk, hsk⟩ := run_first_none m _ hm
    have h3k := run_append k _ _ B3r (asub_run s3 k _ _ hrk)
    -- the s3-run must make a step at time k
    have hstep3 : ∃ L1, step (Ak.map (asub s3) ++ B3r) = some L1 := by
      have := run_add k (m - k) (A.map (asub s3) ++ B3r)
      rw [show k + (m - k) = m by omega, h3, h3k, Option.bind_some] at this
      have hmk : m - k = (m - k - 1) + 1 := by omega
      rw [hmk] at this
      simp only [run] at this
      cases hs : step (Ak.map (asub s3) ++ B3r) with
      | none => rw [hs] at this; simp at this
      | some L1 => exact ⟨L1, rfl⟩
    obtain ⟨L1, hL1⟩ := hstep3
    have hne := run_ne_nil k A Ak hA0 hrk
    match Ak, hrk, hsk, hL1, hne, h3k with
    | [], _, _, _, hne, _ => exact hne rfl
    | f0 :: rest, hrk, hsk, hL1, _, h3k =>
      rcases head_cases f0 with hS | ⟨n, hn⟩
      · -- the abstract run is short: one of the two images is exact
        have hshort : rest.length < 2 := by
          apply Nat.lt_of_not_le
          intro hlen
          have h3l : 3 ≤ (f0 :: rest).length := by simp; omega
          obtain ⟨g, _, hg, hgS⟩ := step_none_len (f0 :: rest) hsk h3l
          injection hg with e _; subst e; exact hgS hS
        rcases hB with hB | hB
        · -- phase 2 is exact and short at time t + k
          subst hB
          have h2 := p2 k _ hrk
          have hstuck : run (t + k + 1) L0 = none := by
            rw [run_add (t + k) 1, h2, Option.bind_some]
            simp only [List.append_nil]
            match rest, hshort with
            | [], _ => simp [run, step]
            | [_], _ => simp [run, step]
          obtain ⟨_, he⟩ := p2stuck k _ hrk hstuck
          simp only [List.append_nil] at he
          have := congrArg List.length he
          simp at this; omega
        · subst hB
          simp only [List.append_nil] at hL1
          match rest, hshort, hL1 with
          | [], _, hL1 => simp [step] at hL1
          | [_], _, hL1 => simp [step] at hL1
      · have hne3 : head (asub s3 f0) ≠ S := by rw [asub_headvar s3 n f0 hn]; exact C1 n
        simp only [List.map_cons, List.cons_append] at hL1
        rw [step_head_ne _ _ hne3] at hL1; simp at hL1
