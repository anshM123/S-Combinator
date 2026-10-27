/-
  agent_work_U/lean/LargePush.lean  (universality agent, 2026-10-27).  Plain Lean 4 core, no Mathlib.

  LARGE-PUSH LEMMA for leftmost Böhm paths of closed S-terms.
  Write a node through its right spine, u = q1 (q2 (... (qd S))) (`LP.ms u` = [q1, ..., qd]).  A leftmost step from
  u = q1.v is a pop (q1 = S, child v), a jump (q1 = S p, child p) or a computed step (q1 with >= 2 arguments); in the
  last case the child is c = q_(k-1)(...(q_0 v)) (`LP.chain_ms`, Lemma 7(iii)).  The step is a LARGE PUSH if some
  pushed q_i is at least as large as q1 (`LP.LargePush`).
  `LP.large_push_lemma`: there is no infinite leftmost walk without large pushes (measure: the stack of multiplier
  sizes in the multiset order, `LP.SStep`, `LP.acc_all`).  Hence an infinite leftmost path has infinitely many large
  pushes; the leftmost-path finite half for a class of terms is equivalent to 'finitely many large pushes'.
  Namespace C = lean/Strip.lean verbatim.
-/

namespace C


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

end C

/-! ## Large-push lemma (namespace LP, closed terms of namespace C) -/

namespace LP

open C
open C.T

/-- right-spine multipliers: u = q1 (q2 (... (qd S))) -/
def ms : T → List T
  | S => []
  | app q v => q :: ms v

/-- one leftmost step of closed terms: the first argument of a node with <= 2 arguments, or the first component of
    the head normal form of a node with >= 3 arguments -/
def Child (u u' : T) : Prop :=
  ((args u).length ≤ 2 ∧ ∃ rest, args u = u' :: rest) ∨
  (3 ≤ (args u).length ∧ ∃ d, Reach (args u) [u', d])

/-- a step from u = q.v to c pushes (on top of the stack v) a multiplier at least as large as q -/
def LargePush (u c : T) : Prop :=
  ∃ q v ps, u = app q v ∧ ms c = ps ++ ms v ∧ ∃ e ∈ ps, size q ≤ size e

theorem ms_size : ∀ (p e : T), e ∈ ms p → size e < size p
  | S, e, h => by simp [ms] at h
  | app q v, e, h => by
    simp only [ms, List.mem_cons] at h
    rcases h with rfl | h
    · have := size_pos v; simp [size]; omega
    · have := ms_size v e h; simp [size]; omega

/-! ### Lemma 7(iii): the child of a computed node extends the stack -/

def LastMs (v : T) (L : List T) : Prop := ∃ M w ps, L = M ++ [w] ∧ ms w = ps ++ ms v

theorem lastms_step (v : T) (L L' : List T) (hB : LastMs v L) (hs : step L = some L') : LastMs v L' := by
  obtain ⟨M, w, ps, rfl, hw⟩ := hB
  match M, hs with
  | [], hs => simp [step] at hs
  | [_], hs => simp [step] at hs
  | [a, b], hs =>
    simp only [List.cons_append, List.nil_append, step, Option.some.injEq] at hs
    subst hs
    exact ⟨args a ++ [w], app b w, b :: ps, by simp, by simp [ms, hw]⟩
  | a :: b :: c :: M', hs =>
    simp only [List.cons_append, step, Option.some.injEq] at hs
    subst hs
    exact ⟨args a ++ c :: app b c :: M', w, ps, by simp, hw⟩

theorem lastms_reach (v : T) (A B : List T) (hA : LastMs v A) (h : Reach A B) : LastMs v B := by
  induction h with
  | refl => exact hA
  | tail _ hs ih => exact lastms_step v _ _ ih hs

theorem lastms_final (v : T) (A : List T) (c d : T) (hA : LastMs v A) (hlen3 : 3 ≤ A.length)
    (h : Reach A [c, d]) : ∃ ps, ms c = ps ++ ms v := by
  cases h with
  | refl => simp at hlen3
  | tail h1 hs =>
    rename_i L1
    obtain ⟨M, w, ps, hL1, hw⟩ := lastms_reach v _ _ hA h1
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
      exact ⟨ps, by rw [← hs.1, ← hw']; exact hw⟩

theorem chain_ms (q v c d : T) (hq : 2 ≤ (args q).length) (h : Reach (args (app q v)) [c, d]) :
    ∃ ps, ms c = ps ++ ms v := by
  rw [args_app] at h
  exact lastms_final v _ c d ⟨args q, v, [], rfl, by simp⟩ (by simp; omega) h

/-! ### the stack order on lists of sizes (top first) -/

/-- replace the top a by elements smaller than a (keeping the rest), or the whole stack by such elements -/
def SStep (L' L : List Nat) : Prop :=
  ∃ a R P, L = a :: R ∧ (∀ x ∈ P, x < a) ∧ (L' = P ++ R ∨ L' = P)

theorem acc_nil : Acc SStep [] := by
  constructor
  intro y hy
  obtain ⟨_, _, _, h, _⟩ := hy
  simp at h

theorem acc_cons_aux : ∀ (n a : Nat), a < n → ∀ R, Acc SStep R → Acc SStep (a :: R) := by
  intro n
  induction n with
  | zero => intro a ha; omega
  | succ n ih =>
    intro a ha R hR
    have hP : ∀ (P : List Nat), (∀ x ∈ P, x < a) → ∀ R', Acc SStep R' → Acc SStep (P ++ R') := by
      intro P
      induction P with
      | nil => intro _ R' h; simpa using h
      | cons b P ihP =>
        intro hb R' hR'
        have hb' : b < a := hb b (by simp)
        have hrest := ihP (fun x hx => hb x (by simp [hx])) R' hR'
        exact ih b (by omega) _ hrest
    constructor
    intro L' hstep
    obtain ⟨a', R', P, hL, hPa, hL'⟩ := hstep
    simp only [List.cons.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    rcases hL' with h' | h'
    · rw [h']; exact hP P hPa R hR
    · rw [h']
      have := hP P hPa [] acc_nil
      simpa using this

theorem acc_all : ∀ L : List Nat, Acc SStep L
  | [] => acc_nil
  | a :: R => acc_cons_aux (a + 1) a (by omega) R (acc_all R)

theorem no_desc (x : List Nat) (hx : Acc SStep x) :
    ∀ f : Nat → List Nat, f 0 = x → (∀ n, SStep (f (n + 1)) (f n)) → False := by
  induction hx with
  | intro x _ ih =>
    intro f h0 hf
    have h1 := hf 0
    rw [h0] at h1
    exact ih (f 1) h1 (fun n => f (n + 1)) rfl (fun n => hf (n + 1))

/-! ### the lemma -/

theorem args_one (q p : T) (h : args q = [p]) : q = app S p := by
  cases q with
  | S => simp [args] at h
  | app f x =>
    simp only [args] at h
    have hl := congrArg List.length h
    simp at hl
    have hf : args f = [] := by
      cases h' : args f with
      | nil => rfl
      | cons _ _ => rw [h'] at hl; simp at hl
    rw [hf] at h
    simp at h
    rw [args_nil f hf, h]

/-- **Large-push lemma.**  A leftmost walk of closed S-terms in which no step is a large push is finite: there is no
    infinite sequence u 0, u 1, ... of leftmost steps none of which pushes a multiplier at least as large as the
    multiplier it pops.  (Measure: the stack of multiplier sizes, top first, in the multiset order.) -/
theorem large_push_lemma (u : Nat → T) (hchild : ∀ j, Child (u j) (u (j + 1)))
    (hnl : ∀ j, ¬ LargePush (u j) (u (j + 1))) : False := by
  apply no_desc _ (acc_all ((ms (u 0)).map size)) (fun j => (ms (u j)).map size) rfl
  intro j
  have hc := hchild j
  have hn := hnl j
  match hu : u j with
  | S =>
    rw [hu] at hc
    rcases hc with ⟨_, rest, h⟩ | ⟨h, _⟩
    · simp [args] at h
    · simp [args] at h
  | app q v =>
    rw [hu] at hc hn
    rcases hc with ⟨hlen, rest, h⟩ | ⟨hlen, d, h⟩
    · rw [args_app] at hlen h
      match hq : args q, h with
      | [], h =>
        -- q = S: pop
        simp only [List.nil_append, List.cons.injEq] at h
        have hqS : q = S := args_nil q hq
        refine ⟨size q, (ms v).map size, [], ?_, by simp, Or.inl ?_⟩
        · simp [ms]
        · rw [← h.1]; simp
      | [p], h =>
        -- q = S p: jump into p
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        have hqp : q = app S p := args_one q p hq
        refine ⟨size q, (ms v).map size, (ms p).map size, by simp [ms], ?_, Or.inr ?_⟩
        · intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨e, he, rfl⟩ := hx
          have := ms_size p e he
          rw [hqp]; simp [size]; omega
        · rw [← h.1]
      | _ :: _ :: _, _ => rw [hq] at hlen; simp at hlen
    · -- computed node: the child is ps over the stack v, all of ps smaller than q
      have hq2 : 2 ≤ (args q).length := by rw [args_app] at hlen; simp at hlen; omega
      obtain ⟨ps, hps⟩ := chain_ms q v _ d hq2 h
      refine ⟨size q, (ms v).map size, ps.map size, by simp [ms], ?_, Or.inl ?_⟩
      · intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨e, he, rfl⟩ := hx
        by_cases hle : size q ≤ size e
        · exact absurd ⟨q, v, ps, rfl, hps, e, he, hle⟩ hn
        · omega
      · rw [hps]; simp

end LP

#print axioms LP.chain_ms
#print axioms LP.large_push_lemma
