
/-! ### Theorem IGEN: if the earlier phase ever lays out args(V) on top of its list (before its transfer), the next
    phase (datum V[y:=p', p:=c]) never reaches a p'-headed front at all. -/

/-- the next-phase substitution: p -> c (frozen), y -> p' = var 0 -/
def sg3 (c : Nat) : Nat → T := fun n => if n = 0 then var c else if n = 2 then var 0 else var n

/-- s3 with three hole atoms H, H+1, H+2 sent to the next phase's inputs y, x.y, r -/
def s3H (c H : Nat) : Nat → T := fun n =>
  if n = 0 then var c else if n = 2 then var 0 else if n = H then var 2 else
  if n = H + 1 then app (var 1) (var 2) else if n = H + 2 then var 3 else var n

/-- s2 with three hole atoms sent to the earlier phase's bottom elements -/
def s2H (H : Nat) (u1 u2 u3 : T) : Nat → T := fun n =>
  if n = H then u1 else if n = H + 1 then u2 else if n = H + 2 then u3 else var n

def fresh3 (H : Nat) (t : T) : Prop := occN H t = 0 ∧ occN (H + 1) t = 0 ∧ occN (H + 2) t = 0

theorem fresh3_args (H : Nat) (t : T) (h : fresh3 H t) : ∀ s ∈ args t, fresh3 H s := by
  intro s hs
  exact ⟨occN_args H t h.1 s hs, occN_args (H + 1) t h.2.1 s hs, occN_args (H + 2) t h.2.2 s hs⟩

theorem asub_s3H (c H : Nat) (hH : 4 ≤ H) : ∀ t : T, fresh3 H t → asub (s3H c H) t = asub (sg3 c) t
  | S, _ => by simp [asub]
  | var n, h => by
    obtain ⟨h1, h2, h3⟩ := h
    have n1 : n ≠ H := by intro e; subst e; simp [occN] at h1
    have n2 : n ≠ H + 1 := by intro e; subst e; simp [occN] at h2
    have n3 : n ≠ H + 2 := by intro e; subst e; simp [occN] at h3
    simp [asub, s3H, sg3, n1, n2, n3]
  | app f x, h => by
    obtain ⟨h1, h2, h3⟩ := h
    simp only [occN] at h1 h2 h3
    simp [asub, asub_s3H c H hH f ⟨by omega, by omega, by omega⟩, asub_s3H c H hH x ⟨by omega, by omega, by omega⟩]

theorem asub_s2H (H : Nat) (u1 u2 u3 : T) : ∀ t : T, fresh3 H t → asub (s2H H u1 u2 u3) t = t
  | S, _ => by simp [asub]
  | var n, h => by
    obtain ⟨h1, h2, h3⟩ := h
    have n1 : n ≠ H := by intro e; subst e; simp [occN] at h1
    have n2 : n ≠ H + 1 := by intro e; subst e; simp [occN] at h2
    have n3 : n ≠ H + 2 := by intro e; subst e; simp [occN] at h3
    simp [asub, s2H, n1, n2, n3]
  | app f x, h => by
    obtain ⟨h1, h2, h3⟩ := h
    simp only [occN] at h1 h2 h3
    simp [asub, asub_s2H H u1 u2 u3 f ⟨by omega, by omega, by omega⟩,
      asub_s2H H u1 u2 u3 x ⟨by omega, by omega, by omega⟩]

theorem s3H_C1 (c H : Nat) : ∀ n, head (s3H c H n) ≠ S := by
  intro n
  simp only [s3H]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp [head]

theorem s3H_C2 (c H : Nat) (hc : c ≠ 0) (hH : 4 ≤ H) (u1 u2 u3 : T) :
    ∀ n, head (s3H c H n) = var 0 → ∃ m, head (s2H H u1 u2 u3 n) = var m ∧ m ≠ 0 := by
  intro n hn
  by_cases h0 : n = 0
  · subst h0; simp [s3H, head, hc] at hn
  by_cases h2 : n = 2
  · subst h2
    refine ⟨2, ?_, by omega⟩
    have a1 : (2 : Nat) ≠ H := by omega
    have a2 : (2 : Nat) ≠ H + 1 := by omega
    have a3 : (2 : Nat) ≠ H + 2 := by omega
    have a4 : H ≠ 0 := by omega
    simp [s2H, a1, a2, a3, a4, head]
  exfalso
  simp only [s3H, h0, h2, ite_false] at hn
  split at hn
  · simp [head] at hn
  · split at hn
    · simp [head] at hn
    · split at hn
      · simp [head] at hn
      · simp [head] at hn; exact h0 hn

theorem args_map_s3H (c H : Nat) (hH : 4 ≤ H) (V : T) (hVS : head V = S) (hV : fresh3 H V) :
    (args V).map (asub (s3H c H)) = args (asub (sg3 c) V) := by
  rw [asub_args (sg3 c) V hVS]
  apply List.map_congr_left
  intro e he
  exact asub_s3H c H hH e (fresh3_args H V hV e he)

theorem args_map_s2H (H : Nat) (u1 u2 u3 : T) (V : T) (hV : fresh3 H V) :
    (args V).map (asub (s2H H u1 u2 u3)) = args V := by
  have : (args V).map (asub (s2H H u1 u2 u3)) = (args V).map id := by
    apply List.map_congr_left
    intro e he
    exact asub_s2H H u1 u2 u3 e (fresh3_args H V hV e he)
  simpa using this

theorem s3H_vals (c H : Nat) (hH : 4 ≤ H) :
    s3H c H H = var 2 ∧ s3H c H (H + 1) = app (var 1) (var 2) ∧ s3H c H (H + 2) = var 3 := by
  have a0 : H ≠ 0 := by omega
  have a2 : H ≠ 2 := by omega
  have b0 : H + 1 ≠ 0 := by omega
  have b2 : H + 1 ≠ 2 := by omega
  have b1 : H + 1 ≠ H := by omega
  have c0 : H + 2 ≠ 0 := by omega
  have c2 : H + 2 ≠ 2 := by omega
  have c1 : H + 2 ≠ H := by omega
  have c3 : H + 2 ≠ H + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [s3H, a0, a2, ite_false, ite_true]
  · simp only [s3H, b0, b2, b1, ite_false, ite_true]
  · simp only [s3H, c0, c2, c1, c3, ite_false, ite_true]

theorem s2H_vals (H : Nat) (u1 u2 u3 : T) :
    s2H H u1 u2 u3 H = u1 ∧ s2H H u1 u2 u3 (H + 1) = u2 ∧ s2H H u1 u2 u3 (H + 2) = u3 := by
  have b1 : H + 1 ≠ H := by omega
  have c1 : H + 2 ≠ H := by omega
  have c3 : H + 2 ≠ H + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [s2H, ite_true]
  · simp only [s2H, b1, ite_false, ite_true]
  · simp only [s2H, c1, c3, ite_false, ite_true]

/-- **THEOREM IGEN.**  Let V be S-headed (the transferred handler) and let a run from L0 (the earlier phase) reach
    a list args(V) ++ B2 at time t and, at a time T' >= t, a list with >= 3 elements whose front is p-headed.  Then
    the run of the next datum V[y:=p', p:=c] never reaches a p'-headed front. -/
theorem igen_main (V : T) (c H : Nat) (hc : c ≠ 0) (hH : 4 ≤ H) (hVS : head V = S) (hVa : args V ≠ []) (hV : fresh3 H V)
    (L0 : List T) (t T' : Nat) (B2 : List T) (htT : t ≤ T') (ht : run t L0 = some (args V ++ B2))
    (f b d : T) (R : List T) (hT : run T' L0 = some (f :: b :: d :: R)) (hf : head f = var 0) :
    ∀ (m : Nat) (f' : T) (L' : List T),
      run m [asub (sg3 c) V, var 1, var 2, var 3] = some (f' :: L') → head f' ≠ var 0 := by
  intro m f' L' h3
  have hD3S : head (asub (sg3 c) V) = S := asub_headS (sg3 c) V hVS
  match m, h3 with
  | 0, h3 =>
    simp [run] at h3; rw [← h3.1, hD3S]; simp
  | m' + 1, h3 =>
    have hs1 : step [asub (sg3 c) V, var 1, var 2, var 3] =
        some (args (asub (sg3 c) V) ++ [var 2, app (var 1) (var 2), var 3]) := by
      simp [step, hD3S]
    simp only [run] at h3
    rw [hs1] at h3
    simp only at h3
    match B2, ht with
    | [], ht =>
      have hA0 : args V ≠ [] := hVa
      apply gcl (args V) hA0 (s2H H S S S) (s3H c H) [] [var 2, app (var 1) (var 2), var 3] (Or.inl rfl)
        (s3H_C1 c H) (s3H_C2 c H hc hH S S S) L0 t T' htT ?_ f b d R hT hf m' f' L' ?_
      · rw [args_map_s2H H S S S V hV]; exact ht
      · rw [args_map_s3H c H hH V hVS hV]; exact h3
    | [u1], ht =>
      apply gcl (args V ++ [var H]) (by simp) (s2H H u1 S S) (s3H c H) [] [app (var 1) (var 2), var 3]
        (Or.inl rfl) (s3H_C1 c H) (s3H_C2 c H hc hH u1 S S) L0 t T' htT ?_ f b d R hT hf m' f' L' ?_
      · rw [List.map_append, args_map_s2H H u1 S S V hV]; simpa [asub, (s2H_vals H _ _ _).1, (s2H_vals H _ _ _).2.1, (s2H_vals H _ _ _).2.2] using ht
      · rw [List.map_append, args_map_s3H c H hH V hVS hV]
        have e1 : asub (s3H c H) (var H) = var 2 := by simp only [asub]; exact (s3H_vals c H hH).1
        rw [List.map_cons, List.map_nil, e1]; simpa using h3
    | [u1, u2], ht =>
      apply gcl (args V ++ [var H, var (H + 1)]) (by simp) (s2H H u1 u2 S) (s3H c H) [] [var 3]
        (Or.inl rfl) (s3H_C1 c H) (s3H_C2 c H hc hH u1 u2 S) L0 t T' htT ?_ f b d R hT hf m' f' L' ?_
      · rw [List.map_append, args_map_s2H H u1 u2 S V hV]; simpa [asub, (s2H_vals H _ _ _).1, (s2H_vals H _ _ _).2.1, (s2H_vals H _ _ _).2.2] using ht
      · rw [List.map_append, args_map_s3H c H hH V hVS hV]
        have e1 : asub (s3H c H) (var H) = var 2 := by simp only [asub]; exact (s3H_vals c H hH).1
        have e2 : asub (s3H c H) (var (H + 1)) = app (var 1) (var 2) := by
          simp only [asub]; exact (s3H_vals c H hH).2.1
        rw [List.map_cons, List.map_cons, List.map_nil, e1, e2]; simpa using h3
    | u1 :: u2 :: u3 :: B2', ht =>
      apply gcl (args V ++ [var H, var (H + 1), var (H + 2)]) (by simp) (s2H H u1 u2 u3) (s3H c H) B2' []
        (Or.inr rfl) (s3H_C1 c H) (s3H_C2 c H hc hH u1 u2 u3) L0 t T' htT ?_ f b d R hT hf m' f' L' ?_
      · rw [List.map_append, args_map_s2H H u1 u2 u3 V hV]; simpa [asub, (s2H_vals H _ _ _).1, (s2H_vals H _ _ _).2.1, (s2H_vals H _ _ _).2.2] using ht
      · rw [List.map_append, args_map_s3H c H hH V hVS hV]
        have e1 : asub (s3H c H) (var H) = var 2 := by simp only [asub]; exact (s3H_vals c H hH).1
        have e2 : asub (s3H c H) (var (H + 1)) = app (var 1) (var 2) := by
          simp only [asub]; exact (s3H_vals c H hH).2.1
        have e3 : asub (s3H c H) (var (H + 2)) = var 3 := by simp only [asub]; exact (s3H_vals c H hH).2.2
        rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, e1, e2, e3]; simpa using h3
