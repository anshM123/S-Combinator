
/-! ##################################################################################################
    R3 agent (2026-10-27): GUARD-FREE replay by pure atom substitution.
    The abstract run of a code g on two fresh 'hole' atoms decides where control goes; both phase 2 and the
    next phase are images of that one abstract run under atom substitutions, so no replay guard is needed.
    ################################################################################################## -/

theorem asub_headS (sg : Nat → T) : ∀ a : T, head a = S → head (asub sg a) = S
  | S, _ => by simp [asub, head]
  | var n, h => by simp [head] at h
  | app f x, h => by
    simp only [asub, head] at h ⊢
    exact asub_headS sg f h

theorem asub_args (sg : Nat → T) : ∀ a : T, head a = S → args (asub sg a) = (args a).map (asub sg)
  | S, _ => by simp [asub, args]
  | var n, h => by simp [head] at h
  | app f x, h => by
    simp only [asub, args, head] at h ⊢
    rw [asub_args sg f h]
    simp

theorem asub_headvar (sg : Nat → T) (n : Nat) : ∀ a : T, head a = var n → head (asub sg a) = head (sg n)
  | S, h => by simp [head] at h
  | var m, h => by simp [head] at h; subst h; simp [asub]
  | app f x, h => by
    simp only [asub, head] at h ⊢
    exact asub_headvar sg n f h

/-- one head step commutes with any atom substitution -/
theorem asub_step (sg : Nat → T) : ∀ (L L' : List T), step L = some L' →
    step (L.map (asub sg)) = some (L'.map (asub sg))
  | a :: b :: d :: R, L', h => by
    simp only [step] at h
    split at h
    · rename_i hS
      injection h with h; subst h
      simp only [List.map_cons, step, asub_headS sg a hS, ite_true, asub_args sg a hS, List.map_append]
      simp [asub]
    · simp at h
  | [], _, h => by simp [step] at h
  | [_], _, h => by simp [step] at h
  | [_, _], _, h => by simp [step] at h

/-- runs commute with any atom substitution (no guard at all) -/
theorem asub_run (sg : Nat → T) : ∀ (k : Nat) (L L' : List T), run k L = some L' →
    run k (L.map (asub sg)) = some (L'.map (asub sg))
  | 0, L, L', h => by simp [run] at h; subst h; simp [run]
  | k + 1, L, L', h => by
    simp only [run] at h ⊢
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      simp only at h
      rw [asub_step sg L L1 hs]
      exact asub_run sg k L1 L' h

/-- if a run stops (step fails) at a list, the substituted run stops there too when the front's head is not
    mapped to an S-headed term -/
theorem step_none_len (L : List T) (h : step L = none) (h3 : 3 ≤ L.length) :
    ∃ f L', L = f :: L' ∧ head f ≠ S := by
  match L, h, h3 with
  | a :: b :: d :: R, h, _ =>
    refine ⟨a, b :: d :: R, rfl, ?_⟩
    intro hS; simp [step, hS] at h
  | [], _, h3 => simp at h3
  | [_], _, h3 => simp at h3
  | [_, _], _, h3 => simp at h3

theorem head_cases : ∀ t : T, head t = S ∨ ∃ n, head t = var n
  | S => Or.inl (by simp [head])
  | var n => Or.inr ⟨n, by simp [head]⟩
  | app f _ => by simp only [head]; exact head_cases f

/-- run arithmetic: a run that stops at step k gives none at every later step -/
theorem run_none_after : ∀ (k j : Nat) (L : List T), run k L = none → k ≤ j → run j L = none
  | k, j, L, h, hkj => by
    have := run_add k (j - k) L
    rw [show k + (j - k) = j by omega, h] at this
    simpa using this
