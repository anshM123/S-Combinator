/-
  agent_work_U/lean/StripV.lean  (universality agent, 2026-10-27).  Plain Lean 4 core, no Mathlib.

  Theorem V, core step, machine-checked: closed code above an untouched variable cannot drive an infinite leftmost
  walk through rounds that keep the variable at the bottom with one closed wrap (k = 1 rounds).
  Namespace C: closed S-terms and the stripping theorem (a verbatim copy of lean/Strip.lean).
  Namespace V: S-terms with variables; head machine with STUCK atom-headed fronts (as in lean/W1F.lean).
  * `V.k1_round`  : if L is a closed list with >= 2 elements and the head run of L ++ [x] (x a variable) reaches a
                    head normal form [w.x, d] with w closed, then the run of L reaches [S S, w], i.e. H(S L) = S (S S) w.
  * `V.no_k1_walk`: there is no infinite sequence of closed W_j (each with >= 2 arguments) such that the head run of
                    W_j.x reaches a head normal form whose first component is W_(j+1).x.
  With W1+ (lean/W1F.lean: survivors of rounds from C ++ [x] are closed or Fibonacci words fib W k) and
  Corollary 8(ii) (lean/BarrierJ.lean) this gives Theorem V of agent_work_U/LOG.md (the remaining case analysis
  over k is on paper).
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

theorem C.args_SS (t : C.T) (h : C.args t = [C.T.S]) : t = C.T.app C.T.S C.T.S := by
  cases t with
  | S => simp [C.args] at h
  | app f x =>
    simp only [C.args] at h
    have hl := congrArg List.length h
    simp at hl
    have hf : C.args f = [] := by
      cases h' : C.args f with
      | nil => rfl
      | cons _ _ => rw [h'] at hl; simp at hl
    rw [hf] at h
    simp at h
    rw [C.args_nil f hf, h]

namespace V

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

/-- closed: no variables -/
def nv : T → Bool
  | S => true
  | var _ => false
  | app f x => nv f && nv x

def step : List T → Option (List T)
  | a :: b :: c :: R => if head a = S then some (args a ++ c :: app b c :: R) else none
  | _ => none

inductive Reach (L0 : List T) : List T → Prop
  | refl : Reach L0 L0
  | tail {L L' : List T} : Reach L0 L → step L = some L' → Reach L0 L'

def X : T := var 0

/-- embedding of closed terms -/
def emb : C.T → T
  | C.T.S => S
  | C.T.app f x => app (emb f) (emb x)

theorem emb_args : ∀ t : C.T, args (emb t) = (C.args t).map emb
  | C.T.S => rfl
  | C.T.app f x => by simp [emb, args, C.args, emb_args f]

theorem head_emb : ∀ t : C.T, head (emb t) = S
  | C.T.S => rfl
  | C.T.app f x => by simp [emb, head, head_emb f]

theorem emb_inj : ∀ a b : C.T, emb a = emb b → a = b
  | C.T.S, C.T.S, _ => rfl
  | C.T.S, C.T.app _ _, h => by simp [emb] at h
  | C.T.app _ _, C.T.S, h => by simp [emb] at h
  | C.T.app f x, C.T.app g y, h => by
    simp only [emb, app.injEq] at h
    rw [emb_inj f g h.1, emb_inj x y h.2]

theorem map_emb_inj : ∀ (A B : List C.T), A.map emb = B.map emb → A = B
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: A, b :: B, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [emb_inj a b h.1, map_emb_inj A B h.2]

theorem step_emb (L : List C.T) : step (L.map emb) = (C.step L).map (List.map emb) := by
  match L with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: R => simp [step, C.step, head_emb, emb_args, emb]

theorem reach_emb_inv (L : List C.T) (M : List T) (h : Reach (L.map emb) M) :
    ∃ L', M = L'.map emb ∧ C.Reach L L' := by
  induction h with
  | refl => exact ⟨L, rfl, C.Reach.refl⟩
  | tail _ hs ih =>
    obtain ⟨L1, rfl, hr⟩ := ih
    rw [step_emb] at hs
    cases h1 : C.step L1 with
    | none => rw [h1] at hs; simp at hs
    | some L2 =>
      rw [h1] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      exact ⟨L2, hs.symm, C.Reach.tail hr h1⟩

theorem step_append (L M : List T) (h3 : 3 ≤ L.length) : step (L ++ M) = (step L).map (· ++ M) := by
  match L, h3 with
  | a :: b :: c :: R, _ =>
    simp only [List.cons_append, step]
    split <;> simp

theorem step_len (L L' : List T) (h : step L = some L') : 2 ≤ L'.length := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; simp; omega
    · simp at h

theorem args_nil_S (t : T) (h1 : args t = []) (h2 : head t = S) : t = S := by
  cases t with
  | S => rfl
  | var n => simp [head] at h2
  | app f x => simp [args] at h1

/-- the final step of a run that ends in a 2-list: [a, b, c] goes to [c, b.c] -/
theorem final_step (L1 : List T) (c d : T) (hs : step L1 = some [c, d]) :
    ∃ a b, L1 = [a, b, c] ∧ d = app b c := by
  match L1, hs with
  | a :: b :: c' :: R, hs =>
    simp only [step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs
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
      exact ⟨a, b, by rw [hs.1], by rw [← hs.2.1, hs.1]⟩
    · simp at hs

/-! ## bottom invariants -/

/-- the last element contains a variable -/
def XBot (L : List T) : Prop := ∃ M w, L = M ++ [w] ∧ nv w = false

theorem xbot_step (L L' : List T) (hB : XBot L) (hs : step L = some L') : XBot L' := by
  obtain ⟨M, w, rfl, hw⟩ := hB
  match M, hs with
  | [], hs => simp [step] at hs
  | [_], hs => simp [step] at hs
  | [a, b], hs =>
    simp only [List.cons_append, List.nil_append, step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      exact ⟨args a ++ [w], app b w, by simp, by simp [nv, hw]⟩
    · simp at hs
  | a :: b :: c :: M', hs =>
    simp only [List.cons_append, step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      exact ⟨args a ++ c :: app b c :: M', w, by simp, hw⟩
    · simp at hs

theorem xbot_reach (A B : List T) (hA : XBot A) (h : Reach A B) : XBot B := by
  induction h with
  | refl => exact hA
  | tail _ hs ih => exact xbot_step _ _ ih hs

/-- a 2-list reachable from a list with a variable at the bottom is the start itself or has a non-closed first
    component -/
theorem xbot_final (A : List T) (c d : T) (hA : XBot A) (h : Reach A [c, d]) : A = [c, d] ∨ nv c = false := by
  cases h with
  | refl => exact Or.inl rfl
  | tail h1 hs =>
    right
    obtain ⟨a, b, rfl, _⟩ := final_step _ c d hs
    obtain ⟨M, w, hM, hw⟩ := xbot_reach _ _ hA h1
    have : w = c := by
      have := congrArg List.getLast? hM
      simp at this; exact this.symm
    rw [← this]; exact hw

/-- the last element is a double wrap a.(b.c) -/
def DBot (L : List T) : Prop := ∃ M a b c, L = M ++ [app a (app b c)]

theorem dbot_step (L L' : List T) (hB : DBot L) (hs : step L = some L') : DBot L' := by
  obtain ⟨M, a0, b0, c0, rfl⟩ := hB
  match M, hs with
  | [], hs => simp [step] at hs
  | [_], hs => simp [step] at hs
  | [a, b], hs =>
    simp only [List.cons_append, List.nil_append, step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      exact ⟨args a ++ [app a0 (app b0 c0)], b, a0, app b0 c0, by simp⟩
    · simp at hs
  | a :: b :: c :: M', hs =>
    simp only [List.cons_append, step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      exact ⟨args a ++ c :: app b c :: M', a0, b0, c0, by simp⟩
    · simp at hs

theorem dbot_reach (A B : List T) (hA : DBot A) (h : Reach A B) : DBot B := by
  induction h with
  | refl => exact hA
  | tail _ hs ih => exact dbot_step _ _ ih hs

theorem dbot_final (A : List T) (c d : T) (hA : DBot A) (h : Reach A [c, d]) :
    A = [c, d] ∨ ∃ a b e, c = app a (app b e) := by
  cases h with
  | refl => exact Or.inl rfl
  | tail h1 hs =>
    right
    obtain ⟨a, b, rfl, _⟩ := final_step _ c d hs
    obtain ⟨M, a0, b0, c0, hM⟩ := dbot_reach _ _ hA h1
    have : app a0 (app b0 c0) = c := by
      have := congrArg List.getLast? hM
      simp at this; exact this.symm
    exact ⟨a0, b0, c0, this.symm⟩

/-! ## the k = 1 round -/

def K1 (L : List T) (L2 : List T) : Prop :=
  (∃ L1, Reach L L1 ∧ 2 ≤ L1.length ∧ L2 = L1 ++ [X]) ∨
  (∃ p q P2, Reach L [p, q] ∧ Reach (args p ++ [X]) P2 ∧ 2 ≤ P2.length ∧ L2 = P2 ++ [app q X]) ∨
  (∃ p q d', Reach L [p, q] ∧ Reach (args p ++ [X]) [S, d'] ∧ L2 = [app q X, app d' (app q X)]) ∨
  (∃ p q c' d', Reach L [p, q] ∧ Reach (args p ++ [X]) [c', d'] ∧ head c' = S ∧ c' ≠ S ∧
      Reach (args c' ++ [app q X, app d' (app q X)]) L2) ∨
  (∃ q, Reach L [S, q] ∧ L2 = [X, app q X])

theorem k1_step (L L2 L3 : List T) (hI : K1 L L2) (hs : step L2 = some L3) : K1 L L3 := by
  rcases hI with ⟨L1, hr, hlen, rfl⟩ | ⟨p, q, P2, hr, hP, hlen, rfl⟩ | ⟨p, q, d', _, _, rfl⟩ |
      ⟨p, q, c', d', hr, hP, hc1, hc2, hr2⟩ | ⟨q, _, rfl⟩
  · by_cases h3 : 3 ≤ L1.length
    · rw [step_append L1 [X] h3] at hs
      cases h1 : step L1 with
      | none => rw [h1] at hs; simp at hs
      | some L1' =>
        rw [h1] at hs
        simp only [Option.map_some, Option.some.injEq] at hs
        subst hs
        exact Or.inl ⟨L1', Reach.tail hr h1, step_len _ _ h1, rfl⟩
    · have h2 : L1.length = 2 := by omega
      match L1, h2, hr, hs with
      | [p, q], _, hr, hs =>
        simp only [List.cons_append, List.nil_append, step] at hs
        split at hs
        · rename_i hp
          simp only [Option.some.injEq] at hs
          subst hs
          by_cases hpa : args p = []
          · have := args_nil_S p hpa hp
            subst this
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, hr, by simp [args]⟩)))
          · refine Or.inr (Or.inl ⟨p, q, args p ++ [X], hr, Reach.refl, ?_, by simp⟩)
            have : 1 ≤ (args p).length := by
              cases h' : args p with
              | nil => exact absurd h' hpa
              | cons _ _ => simp
            simp; omega
        · simp at hs
  · by_cases h3 : 3 ≤ P2.length
    · rw [step_append P2 [app q X] h3] at hs
      cases h1 : step P2 with
      | none => rw [h1] at hs; simp at hs
      | some P2' =>
        rw [h1] at hs
        simp only [Option.map_some, Option.some.injEq] at hs
        subst hs
        exact Or.inr (Or.inl ⟨p, q, P2', hr, Reach.tail hP h1, step_len _ _ h1, rfl⟩)
    · have h2 : P2.length = 2 := by omega
      match P2, h2, hP, hs with
      | [c', d'], _, hP, hs =>
        simp only [List.cons_append, List.nil_append, step] at hs
        split at hs
        · rename_i hc
          simp only [Option.some.injEq] at hs
          subst hs
          by_cases hcS : c' = S
          · subst hcS
            exact Or.inr (Or.inr (Or.inl ⟨p, q, d', hr, hP, by simp [args]⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, c', d', hr, hP, hc, hcS, Reach.refl⟩)))
        · simp at hs
  · simp [step] at hs
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, c', d', hr, hP, hc1, hc2, Reach.tail hr2 hs⟩)))
  · simp [step] at hs

theorem k1_reach (L : List T) (hL : 2 ≤ L.length) (L2 : List T) (h : Reach (L ++ [X]) L2) : K1 L L2 := by
  induction h with
  | refl => exact Or.inl ⟨L, Reach.refl, hL, rfl⟩
  | tail _ hs ih => exact k1_step L _ _ ih hs

/-- **k = 1 round.**  If a closed list L with >= 2 elements, followed by a variable x, reaches the head normal form
    [w.x, d], then the run of L alone reaches [S S, w]:  H(S L) = S (S S) w. -/
theorem k1_round (L0 : List C.T) (w0 : C.T) (d : T) (hL : 2 ≤ L0.length)
    (h : Reach (L0.map emb ++ [X]) [app (emb w0) X, d]) :
    C.Reach L0 [C.T.app C.T.S C.T.S, w0] := by
  have hL' : 2 ≤ (L0.map emb).length := by simp; omega
  rcases k1_reach _ hL' _ h with ⟨L1, _, hlen, hEq⟩ | ⟨p, q, P2, _, _, hlen, hEq⟩ |
      ⟨p, q, d', hr, hP, hEq⟩ | ⟨p, q, c', d', _, _, hc1, hc2, hr2⟩ | ⟨q, _, hEq⟩
  · have := congrArg List.length hEq; simp at this; omega
  · have := congrArg List.length hEq; simp at this; omega
  · simp only [List.cons.injEq, app.injEq] at hEq
    obtain ⟨⟨hq, _⟩, _⟩ := hEq
    obtain ⟨L', hL'eq, hC⟩ := reach_emb_inv L0 [p, q] hr
    match L', hL'eq with
    | [p0, q0], hL'eq =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hL'eq
      obtain ⟨hp0, hq0, _⟩ := hL'eq
      have hx : XBot (args p ++ [X]) := ⟨args p, X, rfl, rfl⟩
      rcases xbot_final _ S d' hx hP with h0 | h0
      · have hpa : args p = [S] := by
          match hp' : args p, h0 with
          | [s], h0 =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at h0
            rw [h0.1]
          | [], h0 => simp at h0
          | _ :: _ :: _, h0 => simp at h0
        rw [hp0, emb_args] at hpa
        have hpa' : C.args p0 = [C.T.S] := map_emb_inj _ [C.T.S] (by simpa [emb] using hpa)
        have hp0' := C.args_SS p0 hpa'
        have hqw : q0 = w0 := by
          apply emb_inj
          rw [← hq0, hq]
        rw [hp0', hqw] at hC
        exact hC
      · simp [nv] at h0
  · exfalso
    have hD : DBot (args c' ++ [app q X, app d' (app q X)]) :=
      ⟨args c' ++ [app q X], d', q, X, by simp⟩
    rcases dbot_final _ _ _ hD hr2 with h0 | ⟨a, b, e, h0⟩
    · have hl := congrArg List.length h0
      simp at hl
      have hca : args c' = [] := by
        cases h' : args c' with
        | nil => rfl
        | cons _ _ => rw [h'] at hl; simp at hl
      exact hc2 (args_nil_S c' hca hc1)
    · simp only [app.injEq] at h0
      obtain ⟨_, h0⟩ := h0
      simp [X] at h0
  · simp only [List.cons.injEq] at hEq
    obtain ⟨h0, _⟩ := hEq
    simp [X] at h0

/-- **No infinite k = 1 walk.**  There is no infinite sequence of closed terms W_j, each with >= 2 arguments, such
    that the head run of W_j.x (x a variable) reaches a head normal form whose first component is W_(j+1).x. -/
theorem no_k1_walk (f : Nat → C.T) (d : Nat → T)
    (h : ∀ j, 2 ≤ (C.args (f j)).length ∧ Reach (args (emb (f j)) ++ [X]) [app (emb (f (j + 1))) X, d j]) :
    False := by
  apply C.no_R2_chain f
  intro j
  obtain ⟨hl, hr⟩ := h j
  rw [emb_args] at hr
  exact k1_round (C.args (f j)) (f (j + 1)) (d j) hl hr

end V

#print axioms V.k1_round
#print axioms V.no_k1_walk
