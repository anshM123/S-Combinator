/-
  agent_work_U/lean/W2.lean  (universality agent, 2026-10-27).  Plain Lean 4 core, no Mathlib.

  Lemma W2 (two opaque data force data execution in a descent-machine round).
  Framework (copied verbatim from the main agent's lean/BarrierJ.lean, which proves Lemma 8, Theorem J and
  Corollary 8(ii)): head machine on lists, [a, b, c] ++ R => args a ++ [c, b.c] ++ R when head a = S; an
  atom-headed front is stuck.  An element is DATA if it contains an atom.

  The descent machine (leftmost-outermost along the leftmost Boehm path) ends a round exactly when the list reaches
  length <= 2 (a head normal form S c d); its next state is c, and d is frozen.  Corollary 8(ii) says: from a list
  with >= 2 data elements, all atom-headed, every data element of a reachable head normal form is atom-headed.
  Applied to a round started from  C ++ [x, y]  (C closed, x, y atoms) this gives:
  * `w2_round`         : every data element of a round-ending list (length <= 2) is atom-headed;
  * `w2_survivor`      : the survivor c of a round ending at [c, d] is closed (all data erased) or atom-headed
                         (the next round starts by executing a datum);
  * `w2_no_code_store` : no round ends with a code-headed survivor that still holds data.
  So in the descent machine two opaque data can never both be kept in a code-controlled state: every round either
  erases all data or hands control to a datum (the DM analogue of Lemma 9 / Theorem J).
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

theorem dv_args (a : T) (h : head a = S) : dv a ≤ dcount (args a) := by
  unfold dv
  cases ha : nv a
  · have := args_data a h ha; simp; omega
  · simp

/-- Lemma 8 (data conservation) -/
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

/-- every data element is atom-headed -/
def dhead (L : List T) : Prop := ∀ e ∈ L, nv e = false → ∃ n, head e = var n

theorem nv_args : ∀ a : T, nv a = true → ∀ e ∈ args a, nv e = true
  | S, _, e, he => by simp [args] at he
  | var _, h, _, _ => by simp [nv] at h
  | app f x, h, e, he => by
    simp only [nv, Bool.and_eq_true] at h
    simp only [args, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact nv_args f h.1 e he
    · exact h.2

/-- Corollary 8(ii) (main agent, lean/BarrierJ.lean, copied verbatim). -/
theorem cor8ii : ∀ (N : Nat) (L1 LN : List T), run N L1 = some LN → LN.length ≤ 2 →
    2 ≤ dcount L1 → dhead L1 → dhead LN
  | 0, L1, LN, h, _, _, hd => by simp [run] at h; subst h; exact hd
  | N + 1, L1, LN, h, hlen, h2, hd => by
    simp only [run] at h
    cases hs : step L1 with
    | none => rw [hs] at h; simp at h
    | some L2 =>
      rw [hs] at h
      match L1, hs, h2, hd with
      | a :: b :: c :: R, hs, h2, hd =>
        simp only [step] at hs
        split at hs
        · rename_i ha
          simp only [Option.some.injEq] at hs
          subst hs
          have hgrow := dcount_step a b c R ha
          have hfin := dcount_run N _ LN h
          have hlenN := dcount_le_length LN
          have hna : nv a = true := by
            cases hv : nv a
            · obtain ⟨n, hn⟩ := hd a (by simp) hv
              rw [ha] at hn
              exact absurd hn (by simp)
            · rfl
          refine cor8ii N _ LN h hlen (by omega) ?_
          intro e he hev
          rcases List.mem_append.1 he with he | he
          · rw [nv_args a hna e he] at hev
            exact absurd hev (by decide)
          · rcases List.mem_cons.1 he with rfl | he
            · exact hd e (by simp) hev
            · rcases List.mem_cons.1 he with rfl | he
              · cases hb : nv b
                · obtain ⟨n, hn⟩ := hd b (by simp) hb
                  exact ⟨n, by simp [head, hn]⟩
                · have hc : nv c = false := by simp [nv, hb] at hev; exact hev
                  have := dcount_write a b c R ha hb hc
                  omega
              · exact hd e (by simp [he]) hev
        · simp at hs

/-! ## Lemma W2 for the descent machine -/

theorem dcount_two_atoms (C : List T) (hC : ∀ x ∈ C, nv x = true) (i j : Nat) :
    dcount (C ++ [var i, var j]) = 2 := by
  have h0 : dcount C = 0 := by
    induction C with
    | nil => simp [dcount]
    | cons x xs ih =>
      have hx : nv x = true := hC x (by simp)
      have hxs : ∀ y ∈ xs, nv y = true := fun y hy => hC y (by simp [hy])
      simp [dcount, hx, ih hxs]
  rw [dcount_append, h0]
  simp [dcount, nv]

theorem dhead_start (C : List T) (hC : ∀ x ∈ C, nv x = true) (i j : Nat) :
    dhead (C ++ [var i, var j]) := by
  intro e he hev
  rcases List.mem_append.1 he with he | he
  · rw [hC e he] at hev; exact absurd hev (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩

/-- **W2.**  A descent-machine round started from C ++ [x, y] (C closed, x, y atoms) that ends — i.e. reaches a list of
    length <= 2 — ends with every data element atom-headed. -/
theorem w2_round (C : List T) (hC : ∀ x ∈ C, nv x = true) (i j N : Nat) (LN : List T)
    (hN : run N (C ++ [var i, var j]) = some LN) (hlen : LN.length ≤ 2) : dhead LN :=
  cor8ii N _ LN hN hlen (by rw [dcount_two_atoms C hC i j]; exact Nat.le_refl 2) (dhead_start C hC i j)

/-- the survivor (first component of the head normal form) is closed or atom-headed -/
theorem w2_survivor (C : List T) (hC : ∀ x ∈ C, nv x = true) (i j N : Nat) (c d : T)
    (hN : run N (C ++ [var i, var j]) = some [c, d]) :
    nv c = true ∨ ∃ n, head c = var n := by
  have hd := w2_round C hC i j N [c, d] hN (by simp)
  cases hc : nv c
  · exact Or.inr (hd c (by simp) hc)
  · exact Or.inl rfl

/-- no round ends with a code-headed survivor that still holds data -/
theorem w2_no_code_store (C : List T) (hC : ∀ x ∈ C, nv x = true) (i j N : Nat) (c d : T)
    (hN : run N (C ++ [var i, var j]) = some [c, d]) (hS : head c = S) : nv c = true := by
  rcases w2_survivor C hC i j N c d hN with h | ⟨n, hn⟩
  · exact h
  · rw [hS] at hn; exact absurd hn (by simp)

#print axioms w2_round
#print axioms w2_survivor
#print axioms w2_no_code_store
