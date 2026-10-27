/-
  Lemma 8 (data conservation), its corollary, and Theorem J (global writes) — machine-checked
  (main agent, 2026-10-27). Plain Lean 4 core, no Mathlib. Framework: the head machine with opaque atoms
  (copied from lean/AgentOC.lean): [a, b, c] ++ R => args a ++ [c, b·c] ++ R when a has head S; an atom-headed front
  is stuck. An element is *data* if it contains an atom.
  * `dcount_step` (Lemma 8): a step never lowers the number of data elements.
  * `no_hnf_of_three_data` (Corollary 8(i)): from a list with >= 3 data elements no list of length <= 2 is reachable.
  * `theoremJ`: in a run that reaches a head normal form, a *write* (b closed, c data) happens only when the data count
    is exactly 1, raises it to exactly 2, and there is at most one write.
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

/-- no atoms (Boolean) -/
def nv : T → Bool
  | S => true
  | var _ => false
  | app f x => nv f && nv x

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

/-- number of data elements (elements containing an atom) -/
def dcount : List T → Nat
  | [] => 0
  | x :: xs => (if nv x then 0 else 1) + dcount xs

theorem dcount_append : ∀ (A B : List T), dcount (A ++ B) = dcount A + dcount B
  | [], B => by simp [dcount]
  | x :: xs, B => by simp [dcount, dcount_append xs B]; omega

theorem dcount_le_length : ∀ L : List T, dcount L ≤ L.length
  | [] => by simp [dcount]
  | x :: xs => by have := dcount_le_length xs; simp [dcount]; split <;> omega

/-- an S-headed term with an atom has an argument with an atom -/
theorem args_data : ∀ a : T, head a = S → nv a = false → 1 ≤ dcount (args a)
  | S, _, h => by simp [nv] at h
  | var _, h, _ => by simp [head] at h
  | app f x, hh, hn => by
    have hf : head f = S := by simpa [head] using hh
    simp only [args, dcount_append]
    simp only [nv, Bool.and_eq_false_iff] at hn
    rcases hn with hf' | hx
    · have := args_data f hf hf'; omega
    · simp [dcount, hx]

/-- data weight of one element -/
def dv (x : T) : Nat := if nv x then 0 else 1

theorem dcount_cons (x : T) (xs : List T) : dcount (x :: xs) = dv x + dcount xs := by simp [dcount, dv]

theorem dv_app_left (b c : T) : dv b ≤ dv (app b c) := by
  unfold dv; simp only [nv]
  by_cases hb : nv b = true <;> by_cases hc : nv c = true <;> simp [hb, hc]

theorem dv_app_right (b c : T) : dv c ≤ dv (app b c) := by
  unfold dv; simp only [nv]
  by_cases hb : nv b = true <;> by_cases hc : nv c = true <;> simp [hb, hc]

theorem dv_args (a : T) (h : head a = S) : dv a ≤ dcount (args a) := by
  unfold dv
  cases ha : nv a
  · have := args_data a h ha; simp; omega
  · simp

/-- **Lemma 8** (data conservation) -/
theorem dcount_step (a b c : T) (R : List T) (h : head a = S) :
    dcount (a :: b :: c :: R) ≤ dcount (args a ++ c :: app b c :: R) := by
  rw [dcount_append]
  simp only [dcount_cons]
  have h1 := dv_args a h
  have h2 := dv_app_left b c
  omega

theorem dcount_step' (L L' : List T) (h : step L = some L') : dcount L ≤ dcount L' := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact dcount_step a b c R (by assumption)
    · simp at h

theorem dcount_run : ∀ (n : Nat) (L L' : List T), run n L = some L' → dcount L ≤ dcount L'
  | 0, L, L', h => by simp [run] at h; subst h; exact Nat.le_refl _
  | n + 1, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 => rw [hs] at h; exact Nat.le_trans (dcount_step' L L1 hs) (dcount_run n L1 L' h)

/-- **Corollary 8(i).** From a list with at least three data elements no head normal form is reachable
    (the run either gets stuck at an atom-headed front or never shrinks below three elements). -/
theorem no_hnf_of_three_data (L : List T) (h3 : 3 ≤ dcount L) :
    ∀ n L', run n L = some L' → 3 ≤ L'.length := by
  intro n L' h
  have := dcount_run n L L' h
  have := dcount_le_length L'
  omega

/-- a write raises the data count by at least one -/
theorem dcount_write (a b c : T) (R : List T) (h : head a = S) (hb : nv b = true) (hc : nv c = false) :
    dcount (a :: b :: c :: R) + 1 ≤ dcount (args a ++ c :: app b c :: R) := by
  rw [dcount_append]
  simp only [dcount_cons]
  have h1 := dv_args a h
  have e1 : dv b = 0 := by simp [dv, hb]
  have e2 : dv c = 1 := by simp [dv, hc]
  have e3 : dv (app b c) = 1 := by simp [dv, nv, hc]
  omega

theorem run_add : ∀ (m n : Nat) (L L' : List T), run m L = some L' → run (m + n) L = run n L'
  | 0, n, L, L', h => by simp [run] at h; subst h; simp
  | m + 1, n, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      rw [show m + 1 + n = (m + n) + 1 by omega]
      simp only [run, hs]; exact run_add m n L1 L' h

/-- **Theorem J** (global writes). Let the run from L0 reach a head normal form LN (length <= 2) at time N.
    If at time k < N the list is [a, b, c] ++ R with a S-headed, b closed and c data (a *write*), then the data count is
    exactly 1 before the write and exactly 2 after it. -/
theorem theoremJ (L0 LN : List T) (N k : Nat) (hN : run N L0 = some LN) (hlen : LN.length ≤ 2)
    (a b c : T) (R : List T) (hk : run k L0 = some (a :: b :: c :: R)) (hkN : k < N)
    (ha : head a = S) (hb : nv b = true) (hc : nv c = false) :
    dcount (a :: b :: c :: R) = 1 ∧ dcount (args a ++ c :: app b c :: R) = 2 := by
  have hs : step (a :: b :: c :: R) = some (args a ++ c :: app b c :: R) := by simp [step, ha]
  have hafter : run (k + 1) L0 = some (args a ++ c :: app b c :: R) := by
    rw [run_add k 1 _ _ hk]; simp [run, hs]
  have hrest : run (N - (k + 1)) (args a ++ c :: app b c :: R) = some LN := by
    have := run_add (k + 1) (N - (k + 1)) _ _ hafter
    rw [show k + 1 + (N - (k + 1)) = N by omega, hN] at this
    exact this.symm
  have h1 := dcount_run _ _ _ hrest
  have h2 := dcount_le_length LN
  have h3 := dcount_write a b c R ha hb hc
  have h4 : 1 ≤ dcount (a :: b :: c :: R) := by
    simp only [dcount_cons]; have : dv c = 1 := by simp [dv, hc]
    omega
  omega

/-- **Theorem J (iii).** In a run that reaches a head normal form there is at most one write. -/
theorem theoremJ_unique (L0 LN : List T) (N k1 k2 : Nat) (hN : run N L0 = some LN) (hlen : LN.length ≤ 2)
    (a1 b1 c1 a2 b2 c2 : T) (R1 R2 : List T)
    (hk1 : run k1 L0 = some (a1 :: b1 :: c1 :: R1)) (hk2 : run k2 L0 = some (a2 :: b2 :: c2 :: R2))
    (h12 : k1 < k2) (hk2N : k2 < N)
    (ha1 : head a1 = S) (hb1 : nv b1 = true) (hc1 : nv c1 = false)
    (ha2 : head a2 = S) (hb2 : nv b2 = true) (hc2 : nv c2 = false) : False := by
  have J1 := theoremJ L0 LN N k1 hN hlen a1 b1 c1 R1 hk1 (by omega) ha1 hb1 hc1
  have J2 := theoremJ L0 LN N k2 hN hlen a2 b2 c2 R2 hk2 hk2N ha2 hb2 hc2
  have hs : step (a1 :: b1 :: c1 :: R1) = some (args a1 ++ c1 :: app b1 c1 :: R1) := by simp [step, ha1]
  have hafter : run (k1 + 1) L0 = some (args a1 ++ c1 :: app b1 c1 :: R1) := by
    rw [run_add k1 1 _ _ hk1]; simp [run, hs]
  have hmid : run (k2 - (k1 + 1)) (args a1 ++ c1 :: app b1 c1 :: R1) = some (a2 :: b2 :: c2 :: R2) := by
    have := run_add (k1 + 1) (k2 - (k1 + 1)) _ _ hafter
    rw [show k1 + 1 + (k2 - (k1 + 1)) = k2 by omega, hk2] at this
    exact this.symm
  have := dcount_run _ _ _ hmid
  omega

/-- **Theorem J (i)** (writes are global): at a write, every other list element is atom-free, so c carries all the data. -/
theorem theoremJ_global (L0 LN : List T) (N k : Nat) (hN : run N L0 = some LN) (hlen : LN.length ≤ 2)
    (a b c : T) (R : List T) (hk : run k L0 = some (a :: b :: c :: R)) (hkN : k < N)
    (ha : head a = S) (hb : nv b = true) (hc : nv c = false) :
    nv a = true ∧ dcount R = 0 := by
  have J := (theoremJ L0 LN N k hN hlen a b c R hk hkN ha hb hc).1
  simp only [dcount_cons] at J
  have e2 : dv c = 1 := by simp [dv, hc]
  have hA : dv a = 0 := by omega
  refine ⟨?_, by omega⟩
  unfold dv at hA
  by_cases h : nv a = true
  · exact h
  · simp [h] at hA

#print axioms theoremJ_global
#print axioms dcount_step
#print axioms no_hnf_of_three_data
#print axioms theoremJ
#print axioms theoremJ_unique
