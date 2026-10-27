/-
  Lemma 5 (Fibonacci peeling) and Lemma 6 (iterator lemma) — machine-checked (main agent, 2026-10-27). Plain Lean 4 core.
  The head machine on lists [a, b, c] ++ R => args a ++ [c, b·c] ++ R, for arbitrary S-terms (no variables needed:
  the arguments q, v, x, c are never opened).
  * `peel` (Lemma 5, general base): [S^(j) z, F_i, F_(i+1)] ++ R reaches [z, F_(i+j), F_(i+j+1)] ++ R in j steps, where
    S^(j) z is the j-fold S(...(S z)) and F_0 = q, F_1 = v, F_(n+2) = F_n · F_(n+1).
  * `peel_nest` (Lemma 5): S N_j q v reaches the head normal form S F_(j+1) F_(j+2) in j + 1 head steps (N_0 = S,
    N_(j+1) = S N_j).
  * `iter_step` (Lemma 6(a)): V_(m+1) x ->1 U x (V_m x) for V_(m+1) = S U V_m; `w_step` (Lemma 6(b)): W_(k+1) c ->1
    S c (W_k c) for W_(k+1) = S S W_k.
-/

inductive Tm where
  | S : Tm
  | app : Tm → Tm → Tm
deriving DecidableEq, Repr

open Tm

def args : Tm → List Tm
  | S => []
  | app f x => args f ++ [x]

def step : List Tm → Option (List Tm)
  | a :: b :: c :: R => some (args a ++ c :: app b c :: R)
  | _ => none

def run : Nat → List Tm → Option (List Tm)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

/-- the Fibonacci words over (q, v) -/
def F (q v : Tm) : Nat → Tm
  | 0 => q
  | 1 => v
  | n + 2 => app (F q v n) (F q v (n + 1))

/-- j-fold S(...(S z)) -/
def Sj (z : Tm) : Nat → Tm
  | 0 => z
  | j + 1 => app S (Sj z j)

/-- **Lemma 5 (general base).** j head steps peel j S's and advance the Fibonacci pair by j. -/
theorem peel (q v z : Tm) (R : List Tm) : ∀ (j i : Nat),
    run j (Sj z j :: F q v i :: F q v (i + 1) :: R) = some (z :: F q v (i + j) :: F q v (i + j + 1) :: R)
  | 0, i => by simp [run, Sj]
  | j + 1, i => by
    have h : step (Sj z (j + 1) :: F q v i :: F q v (i + 1) :: R) =
        some (Sj z j :: F q v (i + 1) :: F q v (i + 2) :: R) := by
      simp [step, Sj, args, F]
    simp only [run, h]
    rw [peel q v z R j (i + 1)]
    simp only [show i + 1 + j = i + (j + 1) by omega]

/-- nests -/
def N : Nat → Tm
  | 0 => S
  | j + 1 => app S (N j)

theorem N_Sj : ∀ j, N j = Sj S j
  | 0 => rfl
  | j + 1 => by simp [N, Sj, N_Sj j]

/-- **Lemma 5 (Fibonacci peeling).** S N_j q v reaches the head normal form S F_(j+1) F_(j+2) in j + 1 head steps. -/
theorem peel_nest (q v : Tm) (j : Nat) : run (j + 1) (args (app (app (app S (N j)) q) v)) = some [F q v (j + 1), F q v (j + 2)] := by
  have e : args (app (app (app S (N j)) q) v) = [N j, F q v 0, F q v 1] := by simp [args, F]
  rw [e, N_Sj]
  have h := peel q v S [] j 0
  -- run (j + 1) = run j then one more step from [S, F_j, F_(j+1)]
  have hsplit : ∀ (m : Nat) (L L' : List Tm), run m L = some L' → run (m + 1) L = run 1 L' := by
    intro m
    induction m with
    | zero => intro L L' h; simp [run] at h; subst h; rfl
    | succ m ih =>
      intro L L' h
      simp only [run] at h ⊢
      cases hs : step L with
      | none => rw [hs] at h; simp at h
      | some L1 => rw [hs] at h; exact ih L1 L' h
  rw [hsplit j _ _ h]
  simp [run, step, args, F, show 0 + j = j by omega]

/-- **Lemma 6(a).** V_(m+1) x ->1 U x (V_m x): one head step turns the list of S U V x into the list of U x (V x). -/
theorem iter_step (U V x : Tm) (R : List Tm) :
    run 1 (args (app (app (app S U) V) x) ++ R) = some (args U ++ x :: app V x :: R) := by
  simp [run, step, args]

/-- **Lemma 6(b).** W_(k+1) c ->1 S c (W_k c) for W_(k+1) = S S W_k: the step leaves the head normal form [c, W_k c]. -/
theorem w_step (W c : Tm) : run 1 (args (app (app (app S S) W) c)) = some [c, app W c] := by
  simp [run, step, args]

#print axioms peel
#print axioms peel_nest
#print axioms w_step
#print axioms iter_step
