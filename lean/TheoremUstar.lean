/-
  Theorem U* (Theorem U survives zero tests) — machine-checked (main agent, 2026-10-27). Plain Lean 4 core.
  Closed head runs with MARKED subterm occurrences (marks may be nested). `mk t` is a marked occurrence of t; data are
  elements that contain a mark. Opening the front consumes every mark on its left spine and exposes its FULL spine
  (`fargs` looks through marks): this is a zero test when the front is data. Step: [a, b, c] ++ R => fargs a ++ [c, b·c] ++ R.
  * F1 (list): closed-prefix ++ data-suffix, i.e. no closed element lies below a data element.
  * F2 (term): the full spine of every subterm occurrence is closed-prefix ++ data-suffix.
  * `ustar_step`, `ustar_run` (Theorem U*): F1 and F2 hold for ever once they hold initially. So a run that starts
    without 'fuel' (a closed element directly below data) never creates any.
-/

inductive MT where
  | S : MT
  | app : MT → MT → MT
  | mk : MT → MT
deriving DecidableEq, Repr

open MT

/-- full spine arguments: marks on the left spine are looked through -/
def fargs : MT → List MT
  | S => []
  | app f a => fargs f ++ [a]
  | mk t => fargs t

/-- contains a mark -/
def hm : MT → Bool
  | S => false
  | app f a => hm f || hm a
  | mk _ => true

def step : List MT → Option (List MT)
  | a :: b :: c :: R => some (fargs a ++ c :: app b c :: R)
  | _ => none

def run : Nat → List MT → Option (List MT)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

/-- F1: no closed element lies below a data element -/
def F1 : List MT → Prop
  | [] => True
  | e :: R => (hm e = true → ∀ f ∈ R, hm f = true) ∧ F1 R

/-- F2: the full spine of every subterm occurrence satisfies F1 -/
def F2 : MT → Prop
  | S => True
  | app f a => F2 f ∧ F2 a ∧ F1 (fargs f ++ [a])
  | mk t => F2 t

theorem F1_append : ∀ (A B : List MT),
    F1 (A ++ B) ↔ F1 A ∧ F1 B ∧ (∀ e ∈ A, hm e = true → ∀ f ∈ B, hm f = true)
  | [], B => by simp [F1]
  | e :: A, B => by
    have ih := F1_append A B
    simp only [List.cons_append, F1]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨h2a, h2b, h2c⟩ := ih.1 h2
      refine ⟨⟨fun he f hf => h1 he f (List.mem_append.2 (Or.inl hf)), h2a⟩, h2b, ?_⟩
      intro e' he' hy' f hf
      rcases List.mem_cons.1 he' with rfl | he'
      · exact h1 hy' f (List.mem_append.2 (Or.inr hf))
      · exact h2c e' he' hy' f hf
    · intro h
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
      refine ⟨?_, ih.2 ⟨h2, h3, fun e' he' => h4 e' (List.mem_cons_of_mem e he')⟩⟩
      intro he f hf
      rcases List.mem_append.1 hf with hf | hf
      · exact h1 he f hf
      · exact h4 e (List.mem_cons_self) he f hf

/-- the full spine of a term satisfies F1 (by F2 at its root) -/
theorem F2_fargs : ∀ t : MT, F2 t → F1 (fargs t)
  | S, _ => by simp [fargs, F1]
  | app f a, h => by simp only [F2] at h; simp only [fargs]; exact h.2.2
  | mk t, h => by simp only [F2] at h; simp only [fargs]; exact F2_fargs t h

/-- every full spine argument satisfies F2 -/
theorem F2_args : ∀ (t e : MT), F2 t → e ∈ fargs t → F2 e
  | S, e, _, he => by simp [fargs] at he
  | app f a, e, h, he => by
    simp only [F2] at h
    simp only [fargs, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact F2_args f e h.1 he
    · exact h.2.1
  | mk t, e, h, he => by simp only [F2] at h; simp only [fargs] at he; exact F2_args t e h he

/-- a closed term has closed full spine arguments -/
theorem closed_args : ∀ (t e : MT), hm t = false → e ∈ fargs t → hm e = false
  | S, e, _, he => by simp [fargs] at he
  | app f a, e, h, he => by
    simp only [hm, Bool.or_eq_false_iff] at h
    simp only [fargs, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact closed_args f e h.1 he
    · exact h.2
  | mk t, e, h, _ => by simp [hm] at h

theorem F1_closed : ∀ L : List MT, (∀ e ∈ L, hm e = false) → F1 L
  | [], _ => trivial
  | e :: R, h => by
    simp only [F1]
    refine ⟨fun he => ?_, F1_closed R (fun f hf => h f (List.mem_cons_of_mem e hf))⟩
    rw [h e List.mem_cons_self] at he
    exact absurd he (by decide)

def UInv (L : List MT) : Prop := F1 L ∧ ∀ e ∈ L, F2 e

/-- **Theorem U\*** (one step): F1 and F2 are preserved, through every zero test. -/
theorem ustar_step (a b c : MT) (R : List MT) (h : UInv (a :: b :: c :: R)) : UInv (fargs a ++ c :: app b c :: R) := by
  obtain ⟨h1, h2⟩ := h
  simp only [F1] at h1
  obtain ⟨hA, hB, hC, hR⟩ := h1
  have F2a := h2 a (by simp)
  have F2b := h2 b (by simp)
  have F2c := h2 c (by simp)
  -- c closed forces b closed
  have cb : hm c = false → hm b = false := by
    intro hc
    cases hb : hm b
    · rfl
    · have := hB hb c (by simp); rw [hc] at this; exact absurd this (by decide)
  refine ⟨?_, ?_⟩
  · rw [F1_append]
    refine ⟨F2_fargs a F2a, ?_, ?_⟩
    · simp only [F1]
      refine ⟨?_, ?_, hR⟩
      · intro hc f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · simp [hm, hc]
        · exact hC hc f hf
      · intro hbc f hf
        simp only [hm, Bool.or_eq_true] at hbc
        rcases hbc with hb | hc
        · exact hB hb f (List.mem_cons_of_mem c hf)
        · exact hC hc f hf
    · intro e he hme f hf
      -- e is a spine argument of a; if a is closed so is e, hence a is data and everything below a is data
      have ha : hm a = true := by
        cases hma : hm a
        · rw [closed_args a e hma he] at hme; exact absurd hme (by decide)
        · rfl
      have hb := hA ha b (by simp)
      have hc := hA ha c (by simp)
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hc
      rcases List.mem_cons.1 hf with rfl | hf
      · simp [hm, hb]
      · exact hA ha f (by simp [hf])
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact F2_args a e F2a he
    rcases List.mem_cons.1 he with rfl | he
    · exact F2c
    rcases List.mem_cons.1 he with rfl | he
    · simp only [F2]
      refine ⟨F2b, F2c, ?_⟩
      rw [F1_append]
      refine ⟨F2_fargs b F2b, by simp [F1], ?_⟩
      intro e' he' hme' f hf
      rw [List.mem_singleton] at hf
      rw [hf]
      cases hc : hm c
      · -- c closed: then b is closed, contradicting the data spine argument e' of b
        rw [closed_args b e' (cb hc) he'] at hme'
        exact absurd hme' (by decide)
      · rfl
    · exact h2 e (by simp [he])

theorem ustar_run : ∀ (n : Nat) (L L' : List MT), UInv L → run n L = some L' → UInv L'
  | 0, L, L', h, hr => by simp [run] at hr; subst hr; exact h
  | n + 1, L, L', h, hr => by
    simp only [run] at hr
    cases hs : step L with
    | none => rw [hs] at hr; simp at hr
    | some L1 =>
      rw [hs] at hr
      apply ustar_run n L1 L' _ hr
      match L, hs, h with
      | a :: b :: c :: R, hs, h =>
        simp only [step, Option.some.injEq] at hs
        subst hs
        exact ustar_step a b c R h

/-- **Theorem U\*.** If the initial list satisfies F1 and F2, every later list does: a run without fuel (no closed element
    directly below data) never creates fuel, whatever zero tests it performs. -/
theorem ustar (L L' : List MT) (n : Nat) (h1 : F1 L) (h2 : ∀ e ∈ L, F2 e) (hr : run n L = some L') :
    F1 L' ∧ ∀ e ∈ L', F2 e :=
  ustar_run n L L' ⟨h1, h2⟩ hr

#print axioms ustar
