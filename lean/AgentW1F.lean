/-
  agent_work_U/lean/W1F.lean  (universality agent, 2026-10-27).  Plain Lean 4 core, no Mathlib.

  Lemma W1+ (Fibonacci classification of single-datum descent-machine rounds).
  Head machine on lists (front first): [a, b, c] ++ R => args a ++ [c, b.c] ++ R when head a = S; atom-headed
  fronts are stuck.  Framework (nv, dcount, Lemma 8, the write lemma) copied from the main agent's
  lean/BarrierJ.lean.  Start: C ++ [x] with C closed and x = var 0 an opaque datum.

  Fibonacci words over (x, W.x):  fib W 0 = x,  fib W 1 = W.x,  fib W (k+2) = (fib W k).(fib W (k+1)).

  `w1f_inv_reach` : every reachable list is  C' ++ [x]  (C' closed), or  C' ++ [fib W k, fib W (k+1)]  (C', W
                    closed), or holds >= 3 data elements.
  `w1f_survivor`  : if a reachable list has length 2 (the descent machine ends its round and continues with the first
                    element c), then c is closed, or c = fib W k for a closed W and some k.
  So the leftmost Boehm path, driven by one opaque datum, can only (i) erase it, (ii) keep it, (iii) add ONE closed
  wrap W, or (iv) copy it by the Fibonacci swap of (x, W.x); no other copying and no second write is possible.
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

inductive Reach (L0 : List T) : List T → Prop
  | refl : Reach L0 L0
  | tail {L L' : List T} : Reach L0 L → step L = some L' → Reach L0 L'

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

def dv (x : T) : Nat := if nv x then 0 else 1

theorem dcount_cons (x : T) (xs : List T) : dcount (x :: xs) = dv x + dcount xs := by simp [dcount, dv]

theorem dv_app_left (b c : T) : dv b ≤ dv (app b c) := by
  unfold dv; simp only [nv]
  by_cases hb : nv b = true <;> by_cases hc : nv c = true <;> simp [hb, hc]

theorem dv_args (a : T) (h : head a = S) : dv a ≤ dcount (args a) := by
  unfold dv
  cases ha : nv a
  · have := args_data a h ha; simp; omega
  · simp

/-- Lemma 8 (data conservation, main agent) -/
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

theorem nv_args : ∀ a : T, nv a = true → ∀ e ∈ args a, nv e = true
  | S, _, e, he => by simp [args] at he
  | var _, h, _, _ => by simp [nv] at h
  | app f x, h, e, he => by
    simp only [nv, Bool.and_eq_true] at h
    simp only [args, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact nv_args f h.1 e he
    · exact h.2

/-! ## Fibonacci words over (x, W.x) -/

def X : T := var 0

def fib (W : T) : Nat → T
  | 0 => X
  | 1 => app W X
  | k + 2 => app (fib W k) (fib W (k + 1))

theorem fib_data (W : T) : ∀ k, nv (fib W k) = false
  | 0 => by simp [fib, X, nv]
  | 1 => by simp [fib, X, nv]
  | k + 2 => by simp [fib, nv, fib_data W k]

def allc (C : List T) : Prop := ∀ y ∈ C, nv y = true

theorem dcount_allc : ∀ C : List T, allc C → dcount C = 0
  | [], _ => by simp [dcount]
  | x :: xs, h => by
    have hx : nv x = true := h x (by simp)
    have hxs : allc xs := fun y hy => h y (by simp [hy])
    simp [dcount, hx, dcount_allc xs hxs]

theorem allc_args (a : T) (ha : nv a = true) : allc (args a) := fun e he => nv_args a ha e he

/-- the invariant: phase 0, phase 1 (Fibonacci pair at the bottom), or >= 3 data elements -/
def FInv (L : List T) : Prop :=
  (∃ C, allc C ∧ L = C ++ [X]) ∨
  (∃ C W k, allc C ∧ nv W = true ∧ L = C ++ [fib W k, fib W (k + 1)]) ∨
  3 ≤ dcount L

theorem finv_step (L L' : List T) (hI : FInv L) (hs : step L = some L') : FInv L' := by
  rcases hI with ⟨C, hC, rfl⟩ | ⟨C, W, k, hC, hW, rfl⟩ | h3
  · -- phase 0
    match C, hC, hs with
    | [], _, hs => simp [step] at hs
    | [_], _, hs => simp [step] at hs
    | [a, b], hC, hs =>
      simp only [List.cons_append, List.nil_append, step] at hs
      split at hs
      · cases hs
        have ha : nv a = true := hC a (by simp)
        have hb : nv b = true := hC b (by simp)
        refine Or.inr (Or.inl ⟨args a, b, 0, allc_args a ha, hb, ?_⟩)
        simp [fib]
      · cases hs
    | a :: b :: c :: C', hC, hs =>
      simp only [List.cons_append, step] at hs
      split at hs
      · cases hs
        have ha : nv a = true := hC a (by simp)
        have hb : nv b = true := hC b (by simp)
        have hc : nv c = true := hC c (by simp)
        refine Or.inl ⟨args a ++ c :: app b c :: C', ?_, by simp⟩
        intro y hy
        simp only [List.mem_append, List.mem_cons] at hy
        rcases hy with hy | hy | hy | hy
        · exact allc_args a ha y hy
        · subst hy; exact hc
        · subst hy; simp [nv, hb, hc]
        · exact hC y (by simp [hy])
      · cases hs
  · -- phase 1
    match C, hC, hs with
    | [], _, hs => simp [step] at hs
    | [a], hC, hs =>
      simp only [List.cons_append, List.nil_append, step] at hs
      split at hs
      · cases hs
        have ha : nv a = true := hC a (by simp)
        refine Or.inr (Or.inl ⟨args a, W, k + 1, allc_args a ha, hW, ?_⟩)
        simp [fib]
      · cases hs
    | [a, b], hC, hs =>
      simp only [List.cons_append, List.nil_append, step] at hs
      split at hs
      · cases hs
        refine Or.inr (Or.inr ?_)
        rw [dcount_append]
        simp [dcount, fib_data W k, fib_data W (k + 1), nv]
      · cases hs
    | a :: b :: c :: C', hC, hs =>
      simp only [List.cons_append, step] at hs
      split at hs
      · cases hs
        have ha : nv a = true := hC a (by simp)
        have hb : nv b = true := hC b (by simp)
        have hc : nv c = true := hC c (by simp)
        refine Or.inr (Or.inl ⟨args a ++ c :: app b c :: C', W, k, ?_, hW, by simp⟩)
        intro y hy
        simp only [List.mem_append, List.mem_cons] at hy
        rcases hy with hy | hy | hy | hy
        · exact allc_args a ha y hy
        · subst hy; exact hc
        · subst hy; simp [nv, hb, hc]
        · exact hC y (by simp [hy])
      · cases hs
  · exact Or.inr (Or.inr (Nat.le_trans h3 (dcount_step' L L' hs)))

theorem w1f_inv_reach (C : List T) (hC : allc C) (L : List T) (hr : Reach (C ++ [X]) L) : FInv L := by
  induction hr with
  | refl => exact Or.inl ⟨C, hC, rfl⟩
  | tail _ hs ih => exact finv_step _ _ ih hs

/-- **W1+.**  The survivor of a round (first element of a reachable 2-list) is closed or a Fibonacci word fib W k
    with W closed. -/
theorem w1f_survivor (C : List T) (hC : allc C) (c d : T) (hr : Reach (C ++ [X]) [c, d]) :
    nv c = true ∨ ∃ W k, nv W = true ∧ c = fib W k := by
  rcases w1f_inv_reach C hC [c, d] hr with ⟨C', hC', hL⟩ | ⟨C', W, k, _, hW, hL⟩ | h3
  · -- [c, d] = C' ++ [X]: C' = [c]
    match C', hC', hL with
    | [c'], hC', hL =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hL
      rw [hL.1]; exact Or.inl (hC' c' (by simp))
    | [], _, hL => simp at hL
    | _ :: _ :: _, _, hL => simp at hL
  · -- [c, d] = C' ++ [fib W k, fib W (k+1)]: C' = []
    match C', hL with
    | [], hL =>
      simp only [List.nil_append, List.cons.injEq] at hL
      exact Or.inr ⟨W, k, hW, hL.1⟩
    | _ :: _, hL =>
      have := congrArg List.length hL
      simp at this
  · have := dcount_le_length [c, d]
    simp at this; omega

#print axioms w1f_inv_reach
#print axioms w1f_survivor
