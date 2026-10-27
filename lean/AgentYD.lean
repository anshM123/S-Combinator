/-
  agent_work/lean/YD.lean  (non-universality agent, 2026-10-27).  Lemma YD: once the bare y has been glued down
  while x.y is the only y-node, no proper y-comb ever exists in the generic run.  Plain Lean 4 core, no Mathlib.
  Atoms: var 1 = x, var 2 = y, var 3 = r; every other atom is opaque (p, frozen values, ...).
  A *proper y-comb* (`pc`) is d1.(d2.(...(dm.y))) with m >= 1 and every d_i free of x, y, r.
  Invariant YDI: no list element is the bare y; no S-headed subterm has the bare y as a spine argument (`nb`);
  every subterm d.y has d = x (`yn`).
-/

inductive T where
  | S : T
  | var : Nat → T
  | app : T → T → T
deriving DecidableEq, Repr

namespace T

def args : T → List T
  | S => []
  | var _ => []
  | app f x => args f ++ [x]

def head : T → T
  | S => S
  | var n => var n
  | app f _ => head f

def occ (n : Nat) : T → Nat
  | S => 0
  | var m => if m = n then 1 else 0
  | app f x => occ n f + occ n x

/-- proper y-comb: d1.(...(dm.y)), m >= 1, wrappers free of x, y, r -/
def pc : T → Prop
  | app d u => occ 1 d = 0 ∧ occ 2 d = 0 ∧ occ 3 d = 0 ∧ (u = var 2 ∨ pc u)
  | _ => False

/-- hereditary: no S-headed subterm has the bare y as a spine argument -/
def nb : T → Prop
  | app f x => (head f = S → x ≠ var 2) ∧ nb f ∧ nb x
  | _ => True

/-- hereditary: every subterm d.y has d = x -/
def yn : T → Prop
  | app f x => (x = var 2 → f = var 1) ∧ yn f ∧ yn x
  | _ => True

end T

open T

def step : List T → Option (List T)
  | a :: b :: c :: R => if head a = S then some (args a ++ c :: app b c :: R) else none
  | _ => none

def run : Nat → List T → Option (List T)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

def YDI (L : List T) : Prop := (∀ e ∈ L, e ≠ var 2) ∧ (∀ e ∈ L, nb e) ∧ (∀ e ∈ L, yn e)

theorem nb_args : ∀ t : T, nb t → ∀ s ∈ args t, nb s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact nb_args f h.2.1 s hs
    · subst hs; exact h.2.2

theorem yn_args : ∀ t : T, yn t → ∀ s ∈ args t, yn s
  | S, _, s, hs => by simp [args] at hs
  | var _, _, s, hs => by simp [args] at hs
  | app f x, h, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · exact yn_args f h.2.1 s hs
    · subst hs; exact h.2.2

/-- an S-headed nb-term has no spine argument equal to the bare y -/
theorem nb_args_ne : ∀ t : T, nb t → head t = S → ∀ s ∈ args t, s ≠ var 2
  | S, _, _, s, hs => by simp [args] at hs
  | var _, _, h, _, _ => by simp [head] at h
  | app f x, h, hS, s, hs => by
    have hf : head f = S := by simpa [head] using hS
    simp [args] at hs
    rcases hs with hs | hs
    · exact nb_args_ne f h.2.1 hf s hs
    · subst hs; exact h.1 hf

theorem ydi_step (a b c : T) (R : List T) (ha : head a = S) (hI : YDI (a :: b :: c :: R)) :
    YDI (args a ++ c :: app b c :: R) := by
  obtain ⟨h0, h1, h2⟩ := hI
  have hc2 : c ≠ var 2 := h0 c (by simp)
  refine ⟨?_, ?_, ?_⟩
  · intro e he; simp at he
    rcases he with he | he | he | he
    · exact nb_args_ne a (h1 a (by simp)) ha e he
    · rw [he]; exact hc2
    · rw [he]; intro h; cases h
    · exact h0 e (by simp [he])
  · intro e he; simp at he
    rcases he with he | he | he | he
    · exact nb_args a (h1 a (by simp)) e he
    · rw [he]; exact h1 c (by simp)
    · rw [he]; exact ⟨fun _ => hc2, h1 b (by simp), h1 c (by simp)⟩
    · exact h1 e (by simp [he])
  · intro e he; simp at he
    rcases he with he | he | he | he
    · exact yn_args a (h2 a (by simp)) e he
    · rw [he]; exact h2 c (by simp)
    · rw [he]; exact ⟨fun h => absurd h hc2, h2 b (by simp), h2 c (by simp)⟩
    · exact h2 e (by simp [he])

theorem ydi_run : ∀ (k : Nat) (L L' : List T), YDI L → run k L = some L' → YDI L'
  | 0, L, L', hI, h => by simp [run] at h; subst h; exact hI
  | k + 1, L, L', hI, h => by
    simp only [run] at h
    split at h
    · rename_i L1 hs
      apply ydi_run k L1 L' _ h
      match L, hs with
      | a :: b :: c :: R, hs =>
        simp only [step] at hs
        split at hs
        · rename_i ha
          injection hs with hs; subst hs
          exact ydi_step a b c R ha hI
        · exact absurd hs (by simp)
    · exact absurd h (by simp)

/-- a yn-term contains no proper y-comb as a subterm (checked at the top: `pc` needs a node d.y with d free of x) -/
theorem yn_not_pc : ∀ t : T, yn t → ¬ pc t
  | S, _, h => h
  | var _, _, h => h
  | app d u, hy, h => by
    obtain ⟨h1, _, _, hu⟩ := h
    rcases hu with hu | hu
    · have := hy.1 hu
      subst this
      simp [occ] at h1
    · exact yn_not_pc u hy.2.2 hu

/-- **Lemma YD (list form).**  From a YDI list, no reachable list has an element that is a proper y-comb; in
    particular no proper transfer (a proper y-comb at position 2 or 3) ever happens. -/
theorem yd_main (k : Nat) (L L' : List T) (hI : YDI L) (h : run k L = some L') : ∀ e ∈ L', ¬ pc e :=
  fun e he => yn_not_pc e ((ydi_run k L L' hI h).2.2 e he)

theorem occ2_nb : ∀ t : T, occ 2 t = 0 → nb t
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => by
    simp only [occ] at h
    refine ⟨fun _ hx => ?_, occ2_nb f (by omega), occ2_nb x (by omega)⟩
    subst hx; simp [occ] at h

theorem occ2_yn : ∀ t : T, occ 2 t = 0 → yn t
  | S, _ => trivial
  | var _, _ => trivial
  | app f x, h => by
    simp only [occ] at h
    refine ⟨fun hx => ?_, occ2_yn f (by omega), occ2_yn x (by omega)⟩
    subst hx; simp [occ] at h

theorem run_succ (k : Nat) (L L' : List T) (hs : step L = some L') : run (k + 1) L = run k L' := by
  simp [run, hs]

/-- **Corollary (bare S outer wrapper).**  A datum S.U with U S-headed and free of y never produces a proper
    y-comb in its generic run [S.U, x, y, r]: the second step glues the bare y onto x.y. -/
theorem yd_bareS (U : T) (hU : occ 2 U = 0) (hS : head U = S) (k : Nat) (L : List T)
    (h : run k [app S U, var 1, var 2, var 3] = some L) : ∀ e ∈ L, ¬ pc e := by
  have hxy : ¬ pc (app (var 1) (var 2)) := fun hp => by simp [pc, occ] at hp
  have hy2 : ¬ pc (var 2) := fun hp => hp
  have hpU : ∀ t : T, occ 2 t = 0 → ¬ pc t := fun t ht => yn_not_pc t (occ2_yn t ht)
  match k, h with
  | 0, h =>
    simp [run] at h; subst h
    intro e he; simp at he
    rcases he with he | he | he | he <;> subst he
    · exact hpU _ (by simp [occ]; exact hU)
    · exact fun hp => hp
    · exact hy2
    · exact fun hp => hp
  | 1, h =>
    simp [run, step, head, args] at h; subst h
    intro e he; simp at he
    rcases he with he | he | he | he <;> subst he
    · exact hpU _ hU
    · exact hy2
    · exact hxy
    · exact fun hp => hp
  | k + 2, h =>
    have s1 : step [app S U, var 1, var 2, var 3] = some [U, var 2, app (var 1) (var 2), var 3] := by
      simp [step, head, args]
    have s2 : step [U, var 2, app (var 1) (var 2), var 3] =
        some (args U ++ [app (var 1) (var 2), app (var 2) (app (var 1) (var 2)), var 3]) := by
      simp [step, hS]
    rw [run_succ _ _ _ s1, run_succ _ _ _ s2] at h
    apply yd_main k _ L _ h
    refine ⟨?_, ?_, ?_⟩
    · intro e he; simp at he
      rcases he with he | he | he | he
      · intro h0; subst h0
        have : occ 2 (var 2) ≠ 0 := by simp [occ]
        exact this (by
          have hle : ∀ t : T, ∀ s ∈ args t, occ 2 s ≤ occ 2 t := by
            intro t; induction t with
            | S => intro s hs; simp [args] at hs
            | var _ => intro s hs; simp [args] at hs
            | app f x ihf _ =>
              intro s hs; simp [args] at hs
              rcases hs with hs | hs
              · have := ihf s hs; simp [occ]; omega
              · subst hs; simp [occ]
          have := hle U (var 2) he; omega)
      · subst he; intro h0; cases h0
      · subst he; intro h0; cases h0
      · subst he; intro h0; cases h0
    · intro e he; simp at he
      rcases he with he | he | he | he
      · have hle : ∀ t : T, occ 2 t = 0 → ∀ s ∈ args t, occ 2 s = 0 := by
          intro t; induction t with
          | S => intro _ s hs; simp [args] at hs
          | var _ => intro _ s hs; simp [args] at hs
          | app f x ihf _ =>
            intro ht s hs; simp only [occ] at ht; simp [args] at hs
            rcases hs with hs | hs
            · exact ihf (by omega) s hs
            · subst hs; omega
        exact occ2_nb e (hle U hU e he)
      · subst he; exact ⟨fun h => by simp [head] at h, trivial, trivial⟩
      · subst he; exact ⟨fun h => by simp [head] at h, trivial, ⟨fun h => by simp [head] at h, trivial, trivial⟩⟩
      · subst he; trivial
    · intro e he; simp at he
      rcases he with he | he | he | he
      · have hle : ∀ t : T, occ 2 t = 0 → ∀ s ∈ args t, occ 2 s = 0 := by
          intro t; induction t with
          | S => intro _ s hs; simp [args] at hs
          | var _ => intro _ s hs; simp [args] at hs
          | app f x ihf _ =>
            intro ht s hs; simp only [occ] at ht; simp [args] at hs
            rcases hs with hs | hs
            · exact ihf (by omega) s hs
            · subst hs; omega
        exact occ2_yn e (hle U hU e he)
      · subst he; exact ⟨fun _ => rfl, trivial, trivial⟩
      · subst he; exact ⟨(fun h => by cases h), trivial, ⟨fun _ => rfl, trivial, trivial⟩⟩
      · subst he; trivial

#print axioms yd_main
#print axioms yd_bareS
