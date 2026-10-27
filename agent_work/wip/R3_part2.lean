
/-! ### two hole atoms are two barriers -/

def isHB (h1 h2 : Nat) (t : T) : Bool := decide (head t = var h1) || decide (head t = var h2)

def nHB (h1 h2 : Nat) : List T → Nat
  | [] => 0
  | e :: L => (if isHB h1 h2 e = true then 1 else 0) + nHB h1 h2 L

theorem nHB_append (h1 h2 : Nat) : ∀ A B : List T, nHB h1 h2 (A ++ B) = nHB h1 h2 A + nHB h1 h2 B
  | [], B => by simp [nHB]
  | e :: A, B => by simp [nHB, nHB_append h1 h2 A B]; omega

theorem isHB_app (h1 h2 : Nat) (b d : T) : isHB h1 h2 (app b d) = isHB h1 h2 b := rfl

theorem isHB_S (h1 h2 : Nat) (a : T) (hS : head a = S) : isHB h1 h2 a = false := by
  simp [isHB, hS]

theorem nHB_step (h1 h2 : Nat) (a b d : T) (R : List T) (hS : head a = S) :
    nHB h1 h2 (a :: b :: d :: R) ≤ nHB h1 h2 (args a ++ d :: app b d :: R) := by
  rw [nHB_append]
  have e1 : nHB h1 h2 (a :: b :: d :: R) = (if isHB h1 h2 a = true then 1 else 0) +
      ((if isHB h1 h2 b = true then 1 else 0) + ((if isHB h1 h2 d = true then 1 else 0) + nHB h1 h2 R)) := rfl
  have e2 : nHB h1 h2 (d :: app b d :: R) = (if isHB h1 h2 d = true then 1 else 0) +
      ((if isHB h1 h2 (app b d) = true then 1 else 0) + nHB h1 h2 R) := rfl
  rw [e1, e2, isHB_app, isHB_S h1 h2 a hS]
  simp only [Bool.false_eq_true, ite_false]
  omega

theorem nHB_run (h1 h2 : Nat) : ∀ (k : Nat) (L L' : List T), run k L = some L' → nHB h1 h2 L ≤ nHB h1 h2 L'
  | 0, L, L', h => by simp [run] at h; subst h; exact Nat.le_refl _
  | k + 1, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      simp only at h
      have ih := nHB_run h1 h2 k L1 L' h
      match L, hs with
      | a :: b :: d :: R, hs =>
        simp only [step] at hs
        split at hs
        · rename_i hS
          injection hs with hs; subst hs
          exact Nat.le_trans (nHB_step h1 h2 a b d R hS) ih
        · simp at hs
      | [], hs => simp [step] at hs
      | [_], hs => simp [step] at hs
      | [_, _], hs => simp [step] at hs

theorem nHB_le_length (h1 h2 : Nat) : ∀ L : List T, nHB h1 h2 L ≤ L.length
  | [] => by simp [nHB]
  | e :: L => by
    have := nHB_le_length h1 h2 L
    simp only [nHB, List.length_cons]
    split <;> omega

/-- with two barriers, a run can only stop at an atom-headed front -/
theorem nHB_stop (h1 h2 : Nat) (L L' : List T) (k : Nat) (h2le : 2 ≤ nHB h1 h2 L)
    (hr : run k L = some L') (hs : step L' = none) : ∃ f rest, L' = f :: rest ∧ head f ≠ S := by
  have hn := Nat.le_trans h2le (nHB_run h1 h2 k L L' hr)
  match L', hn, hs with
  | [], hn, _ => simp [nHB] at hn
  | f :: rest, hn, hs =>
    refine ⟨f, rest, rfl, ?_⟩
    intro hfS
    have hf : isHB h1 h2 f = false := isHB_S h1 h2 f hfS
    simp [nHB, hf] at hn
    have hl := nHB_le_length h1 h2 rest
    have h3 : 3 ≤ (f :: rest).length := by simp; omega
    obtain ⟨f', L'', he, hne⟩ := step_none_len (f :: rest) hs h3
    injection he with he1 _
    rw [← he1] at hne
    exact hne hfS

/-- the first failing step of a run that eventually fails -/
theorem run_first_none : ∀ (j : Nat) (L : List T), run j L = none →
    ∃ k Lk, k < j ∧ run k L = some Lk ∧ step Lk = none
  | 0, L, h => by simp [run] at h
  | j + 1, L, h => by
    simp only [run] at h
    cases hs : step L with
    | none => exact ⟨0, L, by omega, by simp [run], hs⟩
    | some L1 =>
      rw [hs] at h
      simp only at h
      obtain ⟨k, Lk, hk, hrk, hsk⟩ := run_first_none j L1 h
      refine ⟨k + 1, Lk, by omega, ?_, hsk⟩
      simp only [run, hs]
      exact hrk
