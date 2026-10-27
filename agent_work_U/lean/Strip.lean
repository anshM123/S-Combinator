/-
  agent_work_U/lean/Strip.lean  (universality agent, 2026-10-27).  Plain Lean 4 core, no Mathlib.

  Stripping theorem for closed S-terms.  Head machine on argument lists (front first):
  [a, b, c] ++ R  =>  args a ++ [c, b.c] ++ R   (closed terms: every head is S).
  A term P with argument list L has head normal form S c d iff Reach L [c, d].
  * `final_shape` : if L has >= 2 elements and Reach (L ++ [z]) [c, d], then either c = z and the run of L reaches
                    [S, y] with d = y.z  (the bottom z was never wrapped), or c is strictly larger than z.
  * `no_R_chain`  : there is no infinite sequence P0, P1, ... with  H(P_j) = S S P_(j+1).
  * `no_R2_chain` : there is no infinite sequence W0, W1, ... with  H(W_j) = S (S S) W_(j+1).
  (no_R2_chain is the step of the opaque-fuel theorem V in agent_work_U/LOG.md: a leftmost walk of W.x with x a
  variable that never executes x and never drops it performs rounds W_j.x -> W_(j+1).x with H(W_j) = S (S S) W_(j+1).)
-/

inductive T where
  | S : T
  | app : T → T → T
deriving DecidableEq, Repr

open T

def args : T → List T
  | S => []
  | app f x => args f ++ [x]

def size : T → Nat
  | S => 1
  | app f x => size f + size x

def lchild : T → T
  | S => S
  | app f _ => f

def step : List T → Option (List T)
  | a :: b :: c :: R => some (args a ++ c :: app b c :: R)
  | _ => none

inductive Reach (L0 : List T) : List T → Prop
  | refl : Reach L0 L0
  | tail {L L' : List T} : Reach L0 L → step L = some L' → Reach L0 L'

theorem size_pos : ∀ t : T, 0 < size t
  | S => by simp [size]
  | app f x => by have := size_pos f; simp [size]; omega

theorem args_nil (t : T) (h : args t = []) : t = S := by
  cases t with
  | S => rfl
  | app f x => simp [args] at h

theorem size_args : ∀ (t y : T), y ∈ args t → size y < size t
  | S, y, h => by simp [args] at h
  | app f x, y, h => by
    simp only [args, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · have := size_args f y h; simp [size]; omega
    · have := size_pos f; simp [size]; omega

theorem step_len (L L' : List T) (h : step L = some L') : 2 ≤ L'.length := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step, Option.some.injEq] at h; subst h; simp; omega

theorem step_exists (L : List T) (h : 3 ≤ L.length) : ∃ L', step L = some L' := by
  match L, h with
  | a :: b :: c :: R, _ => exact ⟨_, rfl⟩

theorem step_append (L L' M : List T) (h3 : 3 ≤ L.length) (h : step L = some L') :
    step (L ++ M) = some (L' ++ M) := by
  match L, h3, h with
  | a :: b :: c :: R, _, h =>
    simp only [step, Option.some.injEq] at h; subst h
    simp [step]

theorem step_short (A : List T) (hA : A.length ≤ 2) : step A = none := by
  match A, hA with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | _ :: _ :: _ :: _, hA => simp at hA

theorem reach_stuck (A B : List T) (hA : A.length ≤ 2) (h : Reach A B) : B = A := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    rw [ih, step_short A hA] at hs
    exact absurd hs (by simp)

/-! ## the bottom-size invariant -/

/-- the last element is strictly larger than z -/
def BigBot (z : T) (L : List T) : Prop := ∃ M w, L = M ++ [w] ∧ size z < size w

theorem bigbot_step (z : T) (L L' : List T) (hB : BigBot z L) (hs : step L = some L') : BigBot z L' := by
  obtain ⟨M, w, rfl, hw⟩ := hB
  match M, hs with
  | [], hs => simp [step] at hs
  | [_], hs => simp [step] at hs
  | [a, b], hs =>
    simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
    subst hs
    refine ⟨args a ++ [w], app b w, by simp, ?_⟩
    simp [size]; omega
  | a :: b :: c :: M', hs =>
    simp only [List.cons_append, step, Option.some.injEq] at hs
    subst hs
    exact ⟨args a ++ c :: app b c :: M', w, by simp, hw⟩

theorem bigbot_reach (z : T) (A B : List T) (hA : BigBot z A) (h : Reach A B) : BigBot z B := by
  induction h with
  | refl => exact hA
  | tail _ hs ih => exact bigbot_step z _ _ ih hs

/-- a 2-list reached by at least one step from a BigBot list has a first element larger than z -/
theorem bigbot_final (z : T) (A : List T) (c d : T) (hA : BigBot z A) (h : Reach A [c, d])
    (hne : A ≠ [c, d]) : size z < size c := by
  cases h with
  | refl => exact absurd rfl hne
  | tail h1 hs =>
    rename_i L1
    have hB := bigbot_reach z A L1 hA h1
    obtain ⟨M, w, hL1, hw⟩ := hB
    match L1, hs, hL1 with
    | a :: b :: c' :: R, hs, hL1 =>
      simp only [step, Option.some.injEq] at hs
      have hlen := congrArg List.length hs
      simp at hlen
      have ha : args a = [] := by
        cases h' : args a with
        | nil => rfl
        | cons _ _ => rw [h'] at hlen; simp at hlen; omega
      have hR : R = [] := by
        cases R with
        | nil => rfl
        | cons _ _ => simp at hlen; omega
      subst hR
      rw [ha] at hs
      simp only [List.nil_append, List.cons.injEq] at hs
      have hw' : w = c' := by
        have := congrArg List.getLast? hL1
        simp at this; exact this.symm
      rw [← hs.1, ← hw']; exact hw

/-! ## the stripping invariant -/

def SInv (L : List T) (z : T) (L2 : List T) : Prop :=
  (∃ L1, Reach L L1 ∧ 2 ≤ L1.length ∧ L2 = L1 ++ [z]) ∨
  (∃ y, Reach L [S, y] ∧ L2 = [z, app y z]) ∨
  (∃ x y, x ≠ S ∧ Reach L [x, y] ∧ Reach (args x ++ [z, app y z]) L2)

theorem inv_step (L : List T) (z : T) (L2 L3 : List T) (hI : SInv L z L2) (hs : step L2 = some L3) :
    SInv L z L3 := by
  rcases hI with ⟨L1, hr, hlen, rfl⟩ | ⟨y, _, rfl⟩ | ⟨x, y, hx, hr, hr2⟩
  · by_cases h3 : 3 ≤ L1.length
    · obtain ⟨L1', h1'⟩ := step_exists L1 h3
      have := step_append L1 L1' [z] h3 h1'
      rw [this] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact Or.inl ⟨L1', Reach.tail hr h1', step_len _ _ h1', rfl⟩
    · have h2 : L1.length = 2 := by omega
      match L1, h2, hr, hs with
      | [x, y], _, hr, hs =>
        simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
        subst hs
        by_cases hx : x = S
        · subst hx
          exact Or.inr (Or.inl ⟨y, hr, by simp [args]⟩)
        · exact Or.inr (Or.inr ⟨x, y, hx, hr, Reach.refl⟩)
  · simp [step] at hs
  · exact Or.inr (Or.inr ⟨x, y, hx, hr, Reach.tail hr2 hs⟩)

theorem inv_reach (L : List T) (z : T) (hL : 2 ≤ L.length) (L2 : List T) (h : Reach (L ++ [z]) L2) :
    SInv L z L2 := by
  induction h with
  | refl => exact Or.inl ⟨L, Reach.refl, hL, rfl⟩
  | tail _ hs ih => exact inv_step L z _ _ ih hs

/-- **Final shape.**  A head normal form [c, d] of L ++ [z] (L with >= 2 elements) either keeps the bottom z as its
    first component — and then L itself reaches [S, y] and d = y.z — or has a first component larger than z. -/
theorem final_shape (L : List T) (z c d : T) (hL : 2 ≤ L.length) (h : Reach (L ++ [z]) [c, d]) :
    (c = z ∧ ∃ y, Reach L [S, y] ∧ d = app y z) ∨ size z < size c := by
  rcases inv_reach L z hL _ h with ⟨L1, _, hlen, hEq⟩ | ⟨y, hr, hEq⟩ | ⟨x, y, hx, _, hr2⟩
  · have := congrArg List.length hEq; simp at this; omega
  · simp only [List.cons.injEq] at hEq
    exact Or.inl ⟨hEq.1, y, hr, hEq.2.1⟩
  · right
    refine bigbot_final z _ c d ⟨args x ++ [z], app y z, by simp, ?_⟩ hr2 ?_
    · simp [size]; have := size_pos y; omega
    · intro hEq
      have := congrArg List.length hEq
      simp at this
      have : args x = [] := by
        cases h' : args x with
        | nil => rfl
        | cons _ _ => rw [h'] at this; simp at this
      exact hx (args_nil x this)

/-! ## chains -/

/-- H(P) = S S P' -/
def R (P P' : T) : Prop := Reach (args P) [S, P']

/-- H(W) = S (S S) W' -/
def R2 (W W' : T) : Prop := Reach (args W) [app S S, W']

theorem args_app (f x : T) : args (app f x) = args f ++ [x] := rfl

theorem R_short (P P' : T) (h : (args P).length ≤ 2) (hR : R P P') : args P = [S, P'] :=
  (reach_stuck _ _ h hR).symm

theorem R_S (P' : T) : ¬ R S P' := by
  intro h
  have := R_short S P' (by simp [args]) h
  simp [args] at this

/-- if P = Q.z with Q having >= 2 arguments and H(P) = S S P', then z = S and H(Q) = S S y with P' = y.S -/
theorem R_strip (Q z P' : T) (hQ : 2 ≤ (args Q).length) (h : R (app Q z) P') :
    z = S ∧ ∃ y, R Q y ∧ P' = app y S := by
  unfold R at h
  rw [args_app] at h
  rcases final_shape (args Q) z S P' hQ h with ⟨hz, y, hy, hP⟩ | hbig
  · subst hz; exact ⟨rfl, y, hy, hP⟩
  · have := size_pos z; simp [size] at hbig; omega

theorem R2_strip (Q P' : T) (hQ : 2 ≤ (args Q).length) (h : R2 (app Q (app S S)) P') :
    ∃ y, R Q y ∧ P' = app y (app S S) := by
  unfold R2 at h
  rw [args_app] at h
  rcases final_shape (args Q) (app S S) (app S S) P' hQ h with ⟨_, y, hy, hP⟩ | hbig
  · exact ⟨y, hy, hP⟩
  · simp [size] at hbig

/-- a term y.S where y has at most one argument cannot start an R-chain of length 2 -/
theorem R_dies (y P1 P2 : T) (hy : (args y).length ≤ 1) (h1 : R (app y S) P1) (h2 : R P1 P2) : False := by
  have hlen : (args (app y S)).length ≤ 2 := by rw [args_app]; simp; omega
  have e := R_short _ _ hlen h1
  rw [args_app] at e
  match hy' : args y, e with
  | [w], e =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
    rw [← e.2.1] at h2
    exact R_S P2 h2
  | [], e => simp at e
  | _ :: _ :: _, _ => rw [hy'] at hy; simp at hy

theorem no_R_chain_aux : ∀ (n : Nat) (f : Nat → T), size (f 0) ≤ n → (∀ j, R (f j) (f (j + 1))) → False := by
  intro n
  induction n with
  | zero => intro f h _; have := size_pos (f 0); omega
  | succ n ih =>
    intro f hsize hR
    by_cases hshort : (args (f 0)).length ≤ 2
    · have e := R_short _ _ hshort (hR 0)
      have hmem : f 1 ∈ args (f 0) := by rw [e]; simp
      have := size_args _ _ hmem
      exact ih (fun j => f (j + 1)) (by simp; omega) (fun j => hR (j + 1))
    · match hf0 : f 0 with
      | S => rw [hf0] at hshort; simp [args] at hshort
      | app Q z =>
        have hQ : 2 ≤ (args Q).length := by
          rw [hf0, args_app] at hshort; simp at hshort; omega
        have key : ∀ j, f j = app (lchild (f j)) S ∧ 2 ≤ (args (lchild (f j))).length := by
          intro j
          induction j with
          | zero =>
            have h0 := hR 0
            rw [hf0] at h0
            obtain ⟨hz, _⟩ := R_strip Q z (f 1) hQ h0
            subst hz
            rw [hf0]; exact ⟨rfl, hQ⟩
          | succ j ihj =>
            obtain ⟨hfj, hlen⟩ := ihj
            have hj := hR j
            rw [hfj] at hj
            obtain ⟨_, y, _, hP⟩ := R_strip _ S _ hlen hj
            have hy : 2 ≤ (args y).length := by
              by_cases hy1 : (args y).length ≤ 1
              · exfalso
                have h1 := hR (j + 1)
                rw [hP] at h1
                exact R_dies y _ _ hy1 h1 (hR (j + 2))
              · omega
            rw [hP]; exact ⟨rfl, hy⟩
        have chain : ∀ j, R (lchild (f j)) (lchild (f (j + 1))) := by
          intro j
          obtain ⟨hfj, hlen⟩ := key j
          have hj := hR j
          rw [hfj] at hj
          obtain ⟨_, y, hy, hP⟩ := R_strip _ S _ hlen hj
          rw [hP]; exact hy
        have hsz : size (lchild (f 0)) ≤ n := by
          rw [hf0] at hsize ⊢; simp [lchild, size] at hsize ⊢; have := size_pos z; omega
        exact ih (fun j => lchild (f j)) hsz chain

/-- **No infinite R-chain:** there is no sequence P0, P1, ... of closed S-terms with H(P_j) = S S P_(j+1). -/
theorem no_R_chain (f : Nat → T) (hR : ∀ j, R (f j) (f (j + 1))) : False :=
  no_R_chain_aux (size (f 0)) f (Nat.le_refl _) hR

#print axioms no_R_chain

/-! ## R2-chains (the opaque-fuel step) -/

/-- a 2-list reached from a list of length >= 3 has the shape [c, b.c] -/
theorem final_app (A : List T) (c d : T) (hA : 3 ≤ A.length) (h : Reach A [c, d]) : ∃ b, d = app b c := by
  cases h with
  | refl => simp at hA
  | tail h1 hs =>
    rename_i L1
    match L1, hs with
    | a :: b :: c' :: R, hs =>
      simp only [step, Option.some.injEq] at hs
      have hlen := congrArg List.length hs
      simp at hlen
      have ha : args a = [] := by
        cases h' : args a with
        | nil => rfl
        | cons _ _ => rw [h'] at hlen; simp at hlen; omega
      have hR : R = [] := by
        cases R with
        | nil => rfl
        | cons _ _ => simp at hlen; omega
      subst hR
      rw [ha] at hs
      simp only [List.nil_append, List.cons.injEq] at hs
      exact ⟨b, by rw [← hs.2.1, hs.1]⟩

theorem R2_short (W W' : T) (h : (args W).length ≤ 2) (hR : R2 W W') : args W = [app S S, W'] :=
  (reach_stuck _ _ h hR).symm

theorem R2_SS (W' : T) : ¬ R2 (app S S) W' := by
  intro h
  have := R2_short (app S S) W' (by simp [args]) h
  simp [args] at this

theorem R2_dies (y W1 W2 : T) (hy : (args y).length ≤ 1) (h1 : R2 (app y (app S S)) W1)
    (h2 : R2 W1 W2) : False := by
  have hlen : (args (app y (app S S))).length ≤ 2 := by rw [args_app]; simp; omega
  have e := R2_short _ _ hlen h1
  rw [args_app] at e
  match hy' : args y, e with
  | [w], e =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
    rw [← e.2.1] at h2
    exact R2_SS W2 h2
  | [], e => simp at e
  | _ :: _ :: _, _ => rw [hy'] at hy; simp at hy

theorem no_R2_chain_aux : ∀ (n : Nat) (f : Nat → T), size (f 0) ≤ n → (∀ j, R2 (f j) (f (j + 1))) → False := by
  intro n
  induction n with
  | zero => intro f h _; have := size_pos (f 0); omega
  | succ n ih =>
    intro f hsize hR
    by_cases hshort : (args (f 0)).length ≤ 2
    · have e := R2_short _ _ hshort (hR 0)
      have hmem : f 1 ∈ args (f 0) := by rw [e]; simp
      have := size_args _ _ hmem
      exact ih (fun j => f (j + 1)) (by simp; omega) (fun j => hR (j + 1))
    · obtain ⟨b, hb⟩ := final_app _ _ _ (by omega) (hR 0)
      -- from f 1 on, every term is y.(S S) with y having >= 2 arguments
      have key : ∀ j, f (j + 1) = app (lchild (f (j + 1))) (app S S) ∧
          2 ≤ (args (lchild (f (j + 1)))).length := by
        intro j
        induction j with
        | zero =>
          have hb2 : 2 ≤ (args b).length := by
            by_cases hb1 : (args b).length ≤ 1
            · exfalso
              have h1 := hR 1
              rw [hb] at h1
              exact R2_dies b _ _ hb1 h1 (hR 2)
            · omega
          rw [hb]; exact ⟨rfl, hb2⟩
        | succ j ihj =>
          obtain ⟨hfj, hlen⟩ := ihj
          have hj := hR (j + 1)
          rw [hfj] at hj
          obtain ⟨y, _, hP⟩ := R2_strip _ _ hlen hj
          have hy : 2 ≤ (args y).length := by
            by_cases hy1 : (args y).length ≤ 1
            · exfalso
              have h1 := hR (j + 2)
              rw [hP] at h1
              exact R2_dies y _ _ hy1 h1 (hR (j + 3))
            · omega
          rw [hP]; exact ⟨rfl, hy⟩
      have chain : ∀ j, R (lchild (f (j + 1))) (lchild (f (j + 1 + 1))) := by
        intro j
        obtain ⟨hfj, hlen⟩ := key j
        have hj := hR (j + 1)
        rw [hfj] at hj
        obtain ⟨y, hy, hP⟩ := R2_strip _ _ hlen hj
        rw [hP]; exact hy
      exact no_R_chain (fun j => lchild (f (j + 1))) chain

/-- **No infinite R2-chain:** there is no sequence W0, W1, ... of closed S-terms with H(W_j) = S (S S) W_(j+1). -/
theorem no_R2_chain (f : Nat → T) (hR : ∀ j, R2 (f j) (f (j + 1))) : False :=
  no_R2_chain_aux (size (f 0)) f (Nat.le_refl _) hR

#print axioms final_shape
#print axioms no_R2_chain
