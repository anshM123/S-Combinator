/-
  Barrier lemma (PROOF.md, "Barrier lemma and what it gives for loops") — machine-checked (main agent, 2026-10-27).
  Plain Lean 4 core, no Mathlib. Framework: the head machine with opaque atoms (as in lean/BarrierJ.lean):
  [a, b, c] ++ R => args a ++ [c, b·c] ++ R when a has head S; an atom-headed front is stuck.
  A *barrier* is an element whose head is an atom.
  * `barrier_step`: a step never lowers the number of barriers above an untouched tape r (b·c is a barrier iff b is).
  * `barrier_run`: if the part above the tape r holds at least two barriers, every reachable list is L'' ++ r with
    at least two barriers in L'': the tape is never touched.
  * `barrier_lemma`: for every term P and atoms x, y, the run of [P, x, y] ++ r never touches r.
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

/-- barrier: the head is an atom -/
def bar (t : T) : Bool := match head t with
  | var _ => true
  | _ => false

def bcount : List T → Nat
  | [] => 0
  | x :: xs => (if bar x then 1 else 0) + bcount xs

theorem bcount_append : ∀ (A B : List T), bcount (A ++ B) = bcount A + bcount B
  | [], B => by simp [bcount]
  | x :: xs, B => by simp [bcount, bcount_append xs B]; omega

theorem bar_app (b c : T) : bar (app b c) = bar b := by simp [bar, head]

theorem bar_S (a : T) (h : head a = S) : bar a = false := by simp [bar, h]

/-- one step keeps the tape and does not lower the number of barriers above it -/
theorem barrier_step (L' r M : List T) (h2 : 2 ≤ bcount L') (hs : step (L' ++ r) = some M) :
    ∃ L'', M = L'' ++ r ∧ bcount L' ≤ bcount L'' := by
  match L', h2, hs with
  | [], h2, _ => simp [bcount] at h2
  | [u], h2, _ => simp [bcount] at h2; split at h2 <;> omega
  | [u, v], h2, hs =>
    -- both elements are barriers, so the front u is atom-headed and the machine is stuck
    have hu : bar u = true := by
      simp only [bcount] at h2
      cases hb : bar u
      · simp [hb] at h2; split at h2 <;> omega
      · rfl
    match r, hs with
    | [], hs => simp [step] at hs
    | w :: r', hs =>
      simp only [List.cons_append, List.nil_append, step] at hs
      split at hs
      · rename_i ha
        rw [bar_S u ha] at hu
        exact absurd hu (by decide)
      · simp at hs
  | a :: b :: c :: R', _, hs =>
    simp only [List.cons_append, step] at hs
    split at hs
    · rename_i ha
      simp only [Option.some.injEq] at hs
      refine ⟨args a ++ c :: app b c :: R', by rw [← hs]; simp, ?_⟩
      simp only [bcount, bcount_append, bar_app, bar_S a ha]
      simp
      omega
    · simp at hs

/-- the tape below a part with at least two barriers is never touched -/
theorem barrier_run : ∀ (k : Nat) (L' r L : List T), 2 ≤ bcount L' → run k (L' ++ r) = some L →
    ∃ L'', L = L'' ++ r ∧ 2 ≤ bcount L''
  | 0, L', r, L, h2, h => by
    simp [run] at h
    exact ⟨L', h.symm, h2⟩
  | k + 1, L', r, L, h2, h => by
    simp only [run] at h
    cases hs : step (L' ++ r) with
    | none => rw [hs] at h; simp at h
    | some M =>
      rw [hs] at h
      obtain ⟨L'', hM, hc⟩ := barrier_step L' r M h2 hs
      rw [hM] at h
      exact barrier_run k L'' r L (by omega) h

/-- **Barrier lemma.** For every term P and atoms x, y, the head run of [P, x, y] ++ r never touches the tape r. -/
theorem barrier_lemma (P : T) (i j : Nat) (r : List T) (k : Nat) (L : List T)
    (h : run k ([P, var i, var j] ++ r) = some L) : ∃ L'', L = L'' ++ r := by
  have h2 : 2 ≤ bcount [P, var i, var j] := by
    simp only [bcount]
    have e1 : bar (var i) = true := rfl
    have e2 : bar (var j) = true := rfl
    rw [e1, e2]
    simp
    try omega
  obtain ⟨L'', hL, _⟩ := barrier_run k _ r L h2 h
  exact ⟨L'', hL⟩

#print axioms barrier_run
#print axioms barrier_lemma
