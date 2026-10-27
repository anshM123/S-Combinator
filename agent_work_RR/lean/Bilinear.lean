/-
  Theorem B2 (agent_work_RR, 2026-10-27): a bilinear ReplaceAll normalisation time.
  Standalone Lean 4 core. `T`, `pass`, `passN` are verbatim the definitions of agent_work_P/lean/ParTime.lean
  (one ReplaceAll pass: a redex S x y z at the root is contracted without entering x, y, z; otherwise recurse into
  function and argument).  `isNf t` = t contains no redex S x y z.
  numP k = the S-numeral (k+1)-bar = (SS.)^k SS.
  * `lemmaU`: if R becomes normal exactly from pass r on, then (k+1)-bar S R becomes normal exactly from pass
    max(2k+1, k+1+r) on (stated as: normal at pass i iff 2k+1 <= i and k+1+r <= i).
  * `theoremB2`: (j+1)-bar (k+1)-bar S is normal at pass i iff (j+1)(k+1) + 2j <= i; i.e. with n = j+1, m = k+1:
    n_par(n-bar m-bar S) = nm + 2n - 2.
-/

inductive T where
  | S : T
  | var : Nat → T
  | app : T → T → T
deriving DecidableEq, Repr

open T

def pass : T → T
  | S => S
  | var n => var n
  | app (app (app S x) y) a => app (app x a) (app y a)
  | app f a => app (pass f) (pass a)

def passN : Nat → T → T
  | 0, t => t
  | n + 1, t => pass (passN n t)

/-- no redex anywhere -/
def isNf : T → Bool
  | S => true
  | var _ => true
  | app (app (app S _) _) _ => false
  | app f a => isNf f && isNf a

/-- numP k = (k+1)-bar -/
def numP : Nat → T
  | 0 => app S S
  | k + 1 => app (app S S) (numP k)

theorem passN_succ' : ∀ (i : Nat) (t : T), passN (i + 1) t = passN i (pass t)
  | 0, _ => rfl
  | i + 1, t => by
    show pass (passN (i + 1) t) = pass (passN i (pass t))
    rw [passN_succ' i t]

theorem pass_SA (A : T) : pass (app S A) = app S (pass A) := rfl
theorem pass_SAB (A B : T) : pass (app (app S A) B) = app (app S (pass A)) (pass B) := rfl
theorem pass_redex (x y a : T) : pass (app (app (app S x) y) a) = app (app x a) (app y a) := rfl

theorem passN_S : ∀ i : Nat, passN i S = S
  | 0 => rfl
  | i + 1 => by show pass (passN i S) = S; rw [passN_S i]; rfl

theorem passN_SA : ∀ (i : Nat) (A : T), passN i (app S A) = app S (passN i A)
  | 0, _ => rfl
  | i + 1, A => by
    show pass (passN i (app S A)) = app S (pass (passN i A))
    rw [passN_SA i A]; rfl

theorem passN_SAB : ∀ (i : Nat) (A B : T), passN i (app (app S A) B) = app (app S (passN i A)) (passN i B)
  | 0, _, _ => rfl
  | i + 1, A, B => by
    show pass (passN i (app (app S A) B)) = app (app S (pass (passN i A))) (pass (passN i B))
    rw [passN_SAB i A B]; rfl

theorem isNf_SA (A : T) : isNf (app S A) = isNf A := by simp [isNf]
theorem isNf_SAB (A B : T) : isNf (app (app S A) B) = (isNf A && isNf B) := by simp [isNf]
theorem isNf_redex (x y a : T) : isNf (app (app (app S x) y) a) = false := rfl

/-- the numeral step: pass ((k+2)-bar S R) = S S ((k+1)-bar S) (pass R) -/
theorem pass_U_succ (k : Nat) (R : T) :
    pass (app (app (numP (k + 1)) S) R) = app (app (app S S) (app (numP k) S)) (pass R) := rfl
theorem pass_V (X R : T) : pass (app (app (app S S) X) R) = app (app S R) (app X R) := rfl
theorem pass_U_zero (R : T) : pass (app (app (numP 0) S) R) = app (app S R) (app S R) := rfl
theorem isNf_U (k : Nat) (R : T) : isNf (app (app (numP k) S) R) = false := by
  cases k with
  | zero => rfl
  | succ k => simp [numP, isNf]

/-- Lemma U -/
theorem lemmaU : ∀ (k : Nat) (R : T) (r : Nat), (∀ i, isNf (passN i R) = true ↔ r ≤ i) →
    ∀ i, isNf (passN i (app (app (numP k) S) R)) = true ↔ (2 * k + 1 ≤ i ∧ k + 1 + r ≤ i)
  | 0, R, r, hR, i => by
    cases i with
    | zero => simp [passN, isNf_U]
    | succ i =>
      rw [passN_succ', pass_U_zero, passN_SAB, passN_SA, isNf_SAB, isNf_SA]
      simp only [Bool.and_self]
      rw [hR i]; omega
  | k + 1, R, r, hR, i => by
    match i with
    | 0 => simp [passN, isNf_U]
    | 1 =>
      simp only [passN, pass_U_succ]
      constructor
      · intro h; simp [isNf] at h
      · intro h; omega
    | i + 2 =>
      rw [passN_succ', passN_succ', pass_U_succ, pass_V, passN_SAB, isNf_SAB]
      have hR1 : ∀ j, isNf (passN j (pass R)) = true ↔ r - 1 ≤ j := by
        intro j; rw [← passN_succ', hR (j + 1)]; omega
      have ih := lemmaU k (pass R) (r - 1) hR1 i
      rw [Bool.and_eq_true, hR1 i, ih]
      omega

theorem num_S_time : ∀ (k i : Nat), isNf (passN i (app (numP k) S)) = true ↔ k ≤ i
  | 0, i => by
    show isNf (passN i (app (app S S) S)) = true ↔ 0 ≤ i
    rw [passN_SAB, passN_S]; simp [isNf]
  | k + 1, i => by
    cases i with
    | zero => simp [passN, numP, isNf]
    | succ i =>
      rw [passN_succ']
      show isNf (passN i (pass (app (app (app S S) (numP k)) S))) = true ↔ k + 1 ≤ i + 1
      rw [pass_redex, passN_SAB, passN_S, isNf_SAB]
      have hS : isNf S = true := rfl
      rw [hS, Bool.true_and, num_S_time k i]
      omega

theorem le_mul_succ (j k : Nat) : k + 1 ≤ (j + 1) * (k + 1) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.succ_mul]; omega

/-- one numeral applied to another: two passes reach (k+1)-bar S ((j+1)-bar (k+1)-bar S) -/
theorem pass2_B (j k : Nat) :
    pass (pass (app (app (numP (j + 1)) (numP k)) S)) = app (app (numP k) S) (app (app (numP j) (numP k)) S) := rfl

/-- Theorem B2: n_par((j+1)-bar (k+1)-bar S) = (j+1)(k+1) + 2j -/
theorem theoremB2 : ∀ (j k i : Nat),
    isNf (passN i (app (app (numP j) (numP k)) S)) = true ↔ (j + 1) * (k + 1) + 2 * j ≤ i
  | 0, k, i => by
    cases i with
    | zero => simp [passN, numP, isNf]
    | succ i =>
      rw [passN_succ']
      show isNf (passN i (pass (app (app (app S S) (numP k)) S))) = true ↔ (0 + 1) * (k + 1) + 2 * 0 ≤ i + 1
      rw [pass_redex, passN_SAB, passN_S, isNf_SAB]
      have hS : isNf S = true := rfl
      rw [hS, Bool.true_and, num_S_time k i]
      omega
  | j + 1, k, i => by
    match i with
    | 0 => simp [passN, numP, isNf]
    | 1 =>
      constructor
      · intro h; simp [passN, numP, pass, isNf] at h
      · intro h
        have : (j + 1 + 1) * (k + 1) = (j + 1) * (k + 1) + (k + 1) := Nat.succ_mul (j + 1) (k + 1)
        omega
    | i + 2 =>
      rw [passN_succ', passN_succ', pass2_B]
      rw [lemmaU k _ ((j + 1) * (k + 1) + 2 * j) (theoremB2 j k) i]
      have : (j + 1 + 1) * (k + 1) = (j + 1) * (k + 1) + (k + 1) := Nat.succ_mul (j + 1) (k + 1)
      have h2 := le_mul_succ j k
      omega

/-- sanity instances (kernel-checked by evaluation) -/
example : isNf (passN 22 (app (app (numP 3) (numP 3)) S)) = true := by decide
example : isNf (passN 21 (app (app (numP 3) (numP 3)) S)) = false := by decide

#print axioms lemmaU
#print axioms num_S_time
#print axioms theoremB2
