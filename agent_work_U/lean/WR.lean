/-
  agent_work_U/lean/WR.lean  (universality agent, 2026-10-27).  Plain Lean 4 core, no Mathlib.
  COMB RIGIDITY FOR AN ARBITRARY PAIR OF DATA (generalises W2R.lean; framework copied from W1F.lean / the main
  agent's lean/BarrierJ.lean).
  For data u, v (terms containing an atom) let fibP u v 0 = u, fibP u v 1 = v, fibP u v (k+2) = (fibP u v k)(fibP u v (k+1)).
  * `rigid_pair` : if a list of length <= 2 is reachable from C ++ [u, v] (C closed) then C = [] or C = [comb j].
  * `w1r`        : one datum — after the first write [a, b, x] -> args a ++ [x, b.x] (a, b closed) a round can only end
                   if args a = [] or args a = [comb j]: closed pre-computation, ONE write, then a comb.
  * `w2r`        : two data — the code is empty or a comb (this is w2r_rigidity of W2R.lean again).
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



/-! ## Fibonacci words over an arbitrary pair of data -/

def fibP (u v : T) : Nat → T
  | 0 => u
  | 1 => v
  | k + 2 => app (fibP u v k) (fibP u v (k + 1))

theorem fibP_data (u v : T) (hu : nv u = false) (hv : nv v = false) : ∀ k, nv (fibP u v k) = false
  | 0 => hu
  | 1 => hv
  | k + 2 => by simp [fibP, nv, fibP_data u v hu hv k]

def comb : Nat → T
  | 0 => S
  | j + 1 => app S (comb j)

inductive ReachH : List T → List T → Prop
  | refl (L : List T) : ReachH L L
  | step {L L1 L' : List T} : step L = some L1 → ReachH L1 L' → ReachH L L'

def DoomedP (u v : T) (L : List T) : Prop :=
  ∃ C k, allc C ∧ 2 ≤ C.length ∧ L = C ++ [fibP u v k, fibP u v (k + 1)]

theorem doomedP_step (u v : T) (hu : nv u = false) (hv : nv v = false) (L L' : List T)
    (h : DoomedP u v L ∨ 3 ≤ dcount L) (hs : step L = some L') : DoomedP u v L' ∨ 3 ≤ dcount L' := by
  rcases h with ⟨C, k, hC, hlen, rfl⟩ | h3
  · match C, hC, hlen, hs with
    | [a, b], hC, _, hs =>
      simp only [List.cons_append, List.nil_append, step] at hs
      split at hs
      · cases hs
        refine Or.inr ?_
        rw [dcount_append]
        simp [dcount, fibP_data u v hu hv k, fibP_data u v hu hv (k + 1), nv]
      · cases hs
    | a :: b :: c :: C', hC, _, hs =>
      simp only [List.cons_append, step] at hs
      split at hs
      · cases hs
        have ha : nv a = true := hC a (by simp)
        have hb : nv b = true := hC b (by simp)
        have hc : nv c = true := hC c (by simp)
        refine Or.inl ⟨args a ++ c :: app b c :: C', k, ?_, by simp; omega, by simp⟩
        intro y hy
        simp only [List.mem_append, List.mem_cons] at hy
        rcases hy with hy | hy | hy | hy
        · exact allc_args a ha y hy
        · subst hy; exact hc
        · subst hy; simp [nv, hb, hc]
        · exact hC y (by simp [hy])
      · cases hs
    | [], _, hlen, _ => simp at hlen
    | [_], _, hlen, _ => simp at hlen
  · exact Or.inr (Nat.le_trans h3 (dcount_step' L L' hs))

theorem doomedP_reach (u v : T) (hu : nv u = false) (hv : nv v = false) (L L' : List T)
    (hr : ReachH L L') (h : DoomedP u v L ∨ 3 ≤ dcount L) : 3 ≤ L'.length := by
  induction hr with
  | refl L =>
    rcases h with ⟨C, k, _, hlen, rfl⟩ | h3
    · simp; omega
    · have := dcount_le_length L; omega
  | step hs _ ih => exact ih (doomedP_step u v hu hv _ _ h hs)

theorem head_args_nil : ∀ p : T, head p = S → args p = [] → p = S
  | S, _, _ => rfl
  | var _, h, _ => by simp [head] at h
  | app f x, _, h => by simp [args] at h

theorem head_args_single : ∀ p q : T, head p = S → args p = [q] → p = app S q
  | S, _, _, h => by simp [args] at h
  | var _, _, h, _ => by simp [head] at h
  | app f x, q, hh, h => by
    have hf : head f = S := by simpa [head] using hh
    simp only [args] at h
    have hfx : args f = [] ∧ x = q := by
      cases hfa : args f with
      | nil => rw [hfa] at h; simp at h; exact ⟨rfl, h⟩
      | cons y ys => rw [hfa] at h; simp at h
    rw [head_args_nil f hf hfx.1, hfx.2]

theorem combP_rigid (u v : T) (hu : nv u = false) (hv : nv v = false) (L0 L : List T)
    (hr : ReachH L0 L) (hlen : L.length ≤ 2) :
    ∀ p k, L0 = [p, fibP u v k, fibP u v (k + 1)] → nv p = true → ∃ j, p = comb j := by
  induction hr with
  | refl L =>
    intro p k hL _
    subst hL; simp at hlen
  | @step L L1 L' hs hrest ih =>
    intro p k hL hp
    subst hL
    simp only [step] at hs
    split at hs
    · rename_i hha
      simp only [Option.some.injEq] at hs
      subst hs
      cases hap : args p with
      | nil => exact ⟨0, by simp [comb]; exact head_args_nil p hha hap⟩
      | cons q qs =>
        cases qs with
        | nil =>
          have hq : nv q = true := nv_args p hp q (by simp [hap])
          have hpq := head_args_single p q hha hap
          obtain ⟨j, hj⟩ := ih hlen q (k + 1) (by rw [hap]; simp [fibP]) hq
          exact ⟨j + 1, by rw [hpq, hj]; rfl⟩
        | cons q2 qs' =>
          have hC : allc (q :: q2 :: qs') := by
            intro y hy; exact nv_args p hp y (by rw [hap]; exact hy)
          have h3 := doomedP_reach u v hu hv _ L' (by rw [hap] at hrest; simpa [fibP] using hrest)
            (Or.inl ⟨q :: q2 :: qs', k + 1, hC, by simp, rfl⟩)
          omega
    · simp at hs

/-- comb rigidity for an arbitrary pair of data -/
theorem rigid_pair (u v : T) (hu : nv u = false) (hv : nv v = false) (C : List T) (hC : allc C)
    (L : List T) (hr : ReachH (C ++ [u, v]) L) (hlen : L.length ≤ 2) : C = [] ∨ ∃ j, C = [comb j] := by
  match C, hC, hr with
  | [], _, _ => exact Or.inl rfl
  | [p], hC, hr =>
    have hp : nv p = true := hC p (by simp)
    obtain ⟨j, hj⟩ := combP_rigid u v hu hv _ L hr hlen p 0 (by simp [fibP]) hp
    exact Or.inr ⟨j, by rw [hj]⟩
  | p1 :: p2 :: ps, hC, hr =>
    have h3 := doomedP_reach u v hu hv _ L (by simpa [fibP] using hr)
      (Or.inl ⟨p1 :: p2 :: ps, 0, hC, by simp, by simp [fibP]⟩)
    omega

/-- **W1R** (one datum): after the first write the code is empty or a comb. -/
theorem w1r (a b : T) (ha : nv a = true) (L : List T)
    (hr : ReachH (args a ++ [X, app b X]) L) (hlen : L.length ≤ 2) :
    args a = [] ∨ ∃ j, args a = [comb j] :=
  rigid_pair X (app b X) (by simp [X, nv]) (by simp [X, nv]) (args a) (allc_args a ha) L hr hlen

/-- **W2R** (two data) restated through `rigid_pair`. -/
theorem w2r (C : List T) (hC : allc C) (L : List T) (hr : ReachH (C ++ [X, var 1]) L) (hlen : L.length ≤ 2) :
    C = [] ∨ ∃ j, C = [comb j] :=
  rigid_pair X (var 1) (by simp [X, nv]) (by simp [nv]) C hC L hr hlen

#print axioms rigid_pair
#print axioms w1r
#print axioms w2r
