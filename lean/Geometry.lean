/-
  Geometry of head runs — Lemma 7 (iii), the access lemma and Lemma G1 — machine-checked (main agent, 2026-10-27).
  Plain Lean 4 core. The head machine [a, b, c] ++ R => args a ++ [c, b·c] ++ R on S-terms with tags (atoms), an
  atom-headed front being stuck.
  * `last_step` (Lemma 7 (iii)): the last element changes only by last := b·last (for lists of length >= 4 it does not
    change; for length 3 it becomes b·c).
  * `access` (access lemma): an element at position >= 3 (1-based) reaches position 1 or 2 only as c, and only when the
    opened front has at most one spine argument; then b·c, which contains a second copy of it, sits directly below it.
  * `g1_step`, `g1_run` (Lemma G1): while the lowest y-containing element is not at the front, the region T strictly
    below it only loses elements from its top: T(t1) is a suffix of T(t0).
-/

inductive T where
  | S : T
  | var : Nat → T
  | app : T → T → T
deriving DecidableEq, Repr

open T

def args : T → List T
  | S => []
  | var _ => []
  | app f x => args f ++ [x]

def head : T → T
  | S => S
  | var n => var n
  | app f _ => head f

def step : List T → Option (List T)
  | a :: b :: c :: R => if head a = S then some (args a ++ c :: app b c :: R) else none
  | _ => none

def run : Nat → List T → Option (List T)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

/-- **Lemma 7 (iii).** A step keeps the last element when R is non-empty; when R is empty the new last element is b·c
    (last := b·last). -/
theorem last_step (a b c : T) (R : List T) (L' : List T) (h : step (a :: b :: c :: R) = some L') :
    (∀ R0 x, R = R0 ++ [x] → ∃ P', L' = P' ++ [x]) ∧ (R = [] → ∃ P', L' = P' ++ [app b c]) := by
  simp only [step] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun R0 x hR => ⟨args a ++ c :: app b c :: R0, by rw [hR]; simp⟩, fun hR => ⟨args a ++ [c], by rw [hR]; simp⟩⟩
  · simp at h

/-- **Access lemma.** After a step [a, b, c] ++ R => args a ++ [c, b·c] ++ R, the elements at (1-based) positions 1 and
    2 are: two spine arguments of a, or one spine argument of a followed by c, or c followed by b·c. In particular an
    element of R (old position >= 4) never reaches position 1 or 2 in one step, and c (old position 3) reaches position
    1 or 2 only when a has at most one spine argument, with b·c directly below it. -/
theorem access (a b c : T) (R : List T) (L' : List T) (h : step (a :: b :: c :: R) = some L') :
    (2 ≤ (args a).length ∧ L'.take 2 = (args a).take 2) ∨
    ((args a).length = 1 ∧ L'.take 2 = (args a) ++ [c]) ∨
    ((args a).length = 0 ∧ L'.take 2 = [c, app b c]) := by
  simp only [step] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rcases Nat.lt_or_ge (args a).length 2 with hl | hl
    · rcases Nat.lt_or_ge (args a).length 1 with hl1 | hl1
      · have e : args a = [] := List.eq_nil_of_length_eq_zero (by omega)
        right; right; exact ⟨by omega, by simp [e]⟩
      · obtain ⟨x, hx⟩ : ∃ x, args a = [x] := by
          match hq : args a, hl, hl1 with
          | [x], _, _ => exact ⟨x, rfl⟩
          | [], _, h1 => simp at h1
          | _ :: _ :: _, h2, _ => exact absurd h2 (by simp)
        right; left; exact ⟨by simp [hx], by simp [hx]⟩
    · left
      refine ⟨hl, ?_⟩
      rw [List.take_append_of_le_length hl]
  · simp at h

/-! ### Lemma G1 -/

/-- contains the tag y = var 1 -/
def hy : T → Bool
  | S => false
  | var n => n == 1
  | app f x => hy f || hy x

/-- the list splits as P ++ [Y] ++ Tl with Y the lowest y-element (no y in Tl) -/
def lowestSplit (L P Tl : List T) (Y : T) : Prop :=
  L = P ++ Y :: Tl ∧ hy Y = true ∧ ∀ e ∈ Tl, hy e = false

theorem args_noy (a : T) (h : hy a = false) : ∀ e ∈ args a, hy e = false := by
  induction a with
  | S => simp [args]
  | var n => simp [args]
  | app f x ihf _ =>
    simp only [hy, Bool.or_eq_false_iff] at h
    intro e he
    simp only [args, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ihf h.1 e he
    · exact h.2

/-- **Lemma G1 (one step).** If the lowest y-element Y is not at the front (P ≠ []), then after a step the list again
    has a lowest y-element, and the region below it is a suffix of the old region below Y. -/
theorem g1_step (L L' P Tl : List T) (Y : T) (hs : step L = some L') (hsplit : lowestSplit L P Tl Y) (hP : P ≠ []) :
    ∃ P' Y' Tl', lowestSplit L' P' Tl' Y' ∧ ∃ K, Tl = K ++ Tl' := by
  obtain ⟨hL, hY, hT⟩ := hsplit
  subst hL
  match P, hP, hs with
  | [a], _, hs =>
    -- Y is at position 2: [a, Y, c] ++ R => args a ++ [c, Y·c] ++ R; the new lowest y-element is Y·c, below it R
    match Tl, hs, hT with
    | c :: R, hs, hT =>
      simp only [List.singleton_append, step] at hs
      split at hs
      · simp only [Option.some.injEq] at hs
        subst hs
        refine ⟨args a ++ [c], app Y c, R, ⟨by simp, by simp [hy, hY], fun e he => hT e (by simp [he])⟩, [c], rfl⟩
      · simp at hs
    | [], hs, _ => simp [step] at hs
  | [a, b], _, hs =>
    -- Y is at position 3: [a, b, Y] ++ Tl => args a ++ [Y, b·Y] ++ Tl; the new lowest y-element is b·Y, below it Tl
    simp only [List.cons_append, List.nil_append, step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs
      subst hs
      refine ⟨args a ++ [Y], app b Y, Tl, ⟨by simp, by simp [hy, hY], hT⟩, [], rfl⟩
    · simp at hs
  | a :: b :: c :: P0, _, hs =>
    -- Y is at position >= 4: nothing at or below it changes
    simp only [List.cons_append, step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs
      subst hs
      refine ⟨args a ++ c :: app b c :: P0, Y, Tl, ⟨by simp, hY, hT⟩, [], rfl⟩
    · simp at hs

#print axioms last_step
#print axioms access
#print axioms g1_step

theorem run_succ' (k : Nat) (L L1 : List T) (h : step L = some L1) : run (k + 1) L = run k L1 := by
  simp [run, h]

/-- **Lemma G1.** While the lowest y-element is below the front at every step, the region strictly below the lowest
    y-element only loses elements from its top: the final region is a suffix of the initial one. -/
theorem g1_run : ∀ (n : Nat) (L L' P Tl : List T) (Y : T), lowestSplit L P Tl Y → run n L = some L' →
    (∀ k, k < n → ∀ Lk, run k L = some Lk → ∀ Pk Tk Yk, lowestSplit Lk Pk Tk Yk → Pk ≠ []) →
    ∃ P' Y' Tl', lowestSplit L' P' Tl' Y' ∧ ∃ K, Tl = K ++ Tl'
  | 0, L, L', P, Tl, Y, hsp, hr, _ => by
    simp [run] at hr; subst hr
    exact ⟨P, Y, Tl, hsp, [], rfl⟩
  | n + 1, L, L', P, Tl, Y, hsp, hr, hfront => by
    cases hs : step L with
    | none => simp [run, hs] at hr
    | some L1 =>
      rw [run_succ' n L L1 hs] at hr
      have hP := hfront 0 (by omega) L rfl P Tl Y hsp
      obtain ⟨P1, Y1, T1, hsp1, K1, hK1⟩ := g1_step L L1 P Tl Y hs hsp hP
      have hfront1 : ∀ k, k < n → ∀ Lk, run k L1 = some Lk → ∀ Pk Tk Yk, lowestSplit Lk Pk Tk Yk → Pk ≠ [] := by
        intro k hk Lk hLk
        exact hfront (k + 1) (by omega) Lk (by rw [run_succ' k L L1 hs]; exact hLk)
      obtain ⟨P', Y', Tl', hsp', K2, hK2⟩ := g1_run n L1 L' P1 T1 Y1 hsp1 hr hfront1
      exact ⟨P', Y', Tl', hsp', K1 ++ K2, by rw [hK1, hK2, List.append_assoc]⟩

#print axioms g1_run
