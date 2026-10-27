/-
  agent_work_U/lean/W1.lean  (universality agent, 2026-10-27).  Plain Lean 4 core, no Mathlib.

  Lemma W1 (one closed wrap per descent-machine round).
  Head machine on lists (front first):  [a, b, c] ++ R  =>  args a ++ [c, b.c] ++ R   (only if head a = S;
  a front headed by an atom is stuck).  The descent machine (leftmost-outermost along the leftmost Boehm path)
  ends a round exactly when a 3-list [S, b, c] steps to the 2-list [c, b.c]; its next state is c.
  Start: C ++ [D] with C closed and D = var 0 an opaque datum.
  `w1_survivor`: in every reachable 3-list [a, b, c] the bottom c contains D, and if it contains D exactly once
  then c = D or c = w.D with w CLOSED.  So a single-copy survivor carries at most one closed wrap.
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

/-- occurrences of the datum `var 0` -/
def occ : T → Nat
  | S => 0
  | var m => if m = 0 then 1 else 0
  | app f x => occ f + occ x

/-- closed: no atoms -/
def closed : T → Prop
  | S => True
  | var _ => False
  | app f x => closed f ∧ closed x

end T

open T

theorem occ_closed : ∀ x : T, closed x → occ x = 0
  | S, _ => rfl
  | var _, h => absurd h (by simp [closed])
  | app f x, h => by simp [occ, occ_closed f h.1, occ_closed x h.2]

theorem args_closed : ∀ a : T, closed a → ∀ y, y ∈ args a → closed y
  | S, _, y, hy => by simp [args] at hy
  | var _, h, _, _ => absurd h (by simp [closed])
  | app f x, h, y, hy => by
      simp [args] at hy
      rcases hy with hy | hy
      · exact args_closed f h.1 y hy
      · subst hy; exact h.2

def step : List T → Option (List T)
  | a :: b :: c :: R => if head a = S then some (args a ++ c :: app b c :: R) else none
  | _ => none

inductive Reach (L0 : List T) : List T → Prop
  | refl : Reach L0 L0
  | tail {L L' : List T} : Reach L0 L → step L = some L' → Reach L0 L'

def D : T := var 0

theorem occ_D : occ D = 1 := by simp [D, occ]

/-- Phase 0: nothing wrapped yet (closed prefix over the bare datum).
    Phase 1: the bottom B and the element U directly above it both contain D, and a single-copy B is w.D, w closed. -/
def W1Inv (L : List T) : Prop :=
  (∃ C : List T, L = C ++ [D] ∧ ∀ x, x ∈ C → closed x) ∨
  (∃ (P : List T) (U B : T), L = P ++ [U, B] ∧ 0 < occ U ∧ 0 < occ B ∧
      (occ B = 1 → ∃ w, closed w ∧ B = app w D))

theorem inv_step (L L' : List T) (hI : W1Inv L) (hs : step L = some L') : W1Inv L' := by
  rcases hI with ⟨C, hL, hC⟩ | ⟨P, U, B, hL, hU, hB, h1⟩
  · -- phase 0
    subst hL
    match C, hC, hs with
    | [], _, hs => simp [step, D] at hs
    | [_], _, hs => simp [step, D] at hs
    | [a, b], hC, hs =>
      simp only [List.cons_append, List.nil_append, step] at hs
      split at hs
      · cases hs
        have hb : closed b := hC b (by simp)
        refine Or.inr ⟨args a, D, app b D, by simp, ?_, ?_, ?_⟩
        · simp [occ_D]
        · simp [occ, occ_closed b hb, occ_D]
        · intro _; exact ⟨b, hb, rfl⟩
      · cases hs
    | a :: b :: c :: C', hC, hs =>
      simp only [List.cons_append, step] at hs
      split at hs
      · cases hs
        refine Or.inl ⟨args a ++ c :: app b c :: C', by simp, ?_⟩
        intro x hx
        have ha : closed a := hC a (by simp)
        have hb : closed b := hC b (by simp)
        have hc : closed c := hC c (by simp)
        simp at hx
        rcases hx with hx | hx | hx | hx
        · exact args_closed a ha x hx
        · subst hx; exact hc
        · subst hx; exact ⟨hb, hc⟩
        · exact hC x (by simp [hx])
      · cases hs
  · -- phase 1
    subst hL
    match P, hs with
    | [], hs => simp [step] at hs
    | [a], hs =>
      simp only [List.cons_append, List.nil_append, step] at hs
      split at hs
      · cases hs
        refine Or.inr ⟨args a, B, app U B, by simp, hB, ?_, ?_⟩
        · simp [occ]; omega
        · intro h; simp [occ] at h; omega
      · cases hs
    | [a, b], hs =>
      simp only [List.cons_append, List.nil_append, step] at hs
      split at hs
      · cases hs
        refine Or.inr ⟨args a ++ [U], app b U, B, by simp, ?_, hB, h1⟩
        simp [occ]; omega
      · cases hs
    | a :: b :: c :: P', hs =>
      simp only [List.cons_append, step] at hs
      split at hs
      · cases hs
        exact Or.inr ⟨args a ++ c :: app b c :: P', U, B, by simp, hU, hB, h1⟩
      · cases hs

theorem inv_reach (L0 L : List T) (h0 : W1Inv L0) (hr : Reach L0 L) : W1Inv L := by
  induction hr with
  | refl => exact h0
  | tail _ hs ih => exact inv_step _ _ ih hs

/-- Lemma W1. -/
theorem w1_survivor (C : List T) (hC : ∀ x, x ∈ C → closed x) (a b c : T)
    (hr : Reach (C ++ [D]) [a, b, c]) :
    0 < occ c ∧ (occ c = 1 → c = D ∨ ∃ w, closed w ∧ c = app w D) := by
  have hI : W1Inv [a, b, c] := inv_reach _ _ (Or.inl ⟨C, rfl, hC⟩) hr
  rcases hI with ⟨C', hL, _⟩ | ⟨P, U, B, hL, _, hB, h1⟩
  · -- [a, b, c] = C' ++ [D]
    have hc : c = D := by
      have := congrArg List.getLast? hL
      simpa using this
    subst hc
    exact ⟨by simp [occ_D], fun _ => Or.inl rfl⟩
  · have hc : c = B := by
      have := congrArg List.getLast? hL
      simpa using this
    subst hc
    exact ⟨hB, fun h => Or.inr (h1 h)⟩
