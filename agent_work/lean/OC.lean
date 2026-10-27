/-
  agent_work/lean/OC.lean  (construction agent, 2026-10-26).  Plain Lean 4 core, no Mathlib.

  Lemma OC (occurrence counting) and Corollary OC1 for the head machine with opaque atoms:
     [a, b, c] ++ R  =>  args a ++ [c, b.c] ++ R      (only when a has head S; an atom-headed front is stuck)
  * `occL_step`  : the number of occurrences of an atom grows by exactly its number of occurrences in the third element.
  * `oc1`        : for a closed term T with at least one argument (T != S), every stuck list reachable from
                   [T, u, v, r] contains at least three occurrences of v.
  * `no_transparent` : hence no closed T != S has a generic activation rule of the form
                   [v.w..., (u.v).w'..., rest...] with all w, w', rest closed.
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

/-- number of occurrences of atom n -/
def occ (n : Nat) : T → Nat
  | S => 0
  | var m => if m = n then 1 else 0
  | app f x => occ n f + occ n x

/-- closed: no atoms -/
def closed : T → Prop
  | S => True
  | var _ => False
  | app f x => closed f ∧ closed x

end T

open T

def occL (n : Nat) : List T → Nat
  | [] => 0
  | x :: xs => occ n x + occL n xs

theorem occL_append (n : Nat) : ∀ (A B : List T), occL n (A ++ B) = occL n A + occL n B
  | [], B => by simp [occL]
  | x :: xs, B => by simp [occL, occL_append n xs B]; omega

/-- for an S-headed term, all atom occurrences lie in its arguments -/
theorem occ_args (n : Nat) : ∀ a : T, head a = S → occL n (args a) = occ n a
  | S, _ => by simp [args, occL, occ]
  | var m, h => by simp [head] at h
  | app f x, h => by
    have hf : head f = S := by simpa [head] using h
    simp [args, occ, occL_append, occ_args n f hf, occL]

/-- one machine step; atom-headed fronts are stuck -/
def step : List T → Option (List T)
  | a :: b :: c :: R => if head a = S then some (args a ++ c :: app b c :: R) else none
  | _ => none

def run : Nat → List T → Option (List T)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

/-- Lemma OC -/
theorem occL_step (n : Nat) (a b c : T) (R : List T) (h : head a = S) :
    occL n (args a ++ c :: app b c :: R) = occL n (a :: b :: c :: R) + occ n c := by
  rw [occL_append, occ_args n a h]
  simp [occL, occ]
  omega

theorem occL_step_ge (n : Nat) (L L' : List T) (h : step L = some L') : occL n L ≤ occL n L' := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step] at h
    split at h
    · rename_i ha
      injection h with h; subst h
      rw [occL_step n a b c R ha]; omega
    · exact absurd h (by simp)

theorem closed_head (t : T) (h : closed t) : head t = S := by
  induction t with
  | S => rfl
  | var m => simp [closed] at h
  | app f x ihf _ => simp [head]; exact ihf h.1

theorem closed_args : ∀ t : T, closed t → ∀ x ∈ args t, closed x
  | S, _ => by simp [args]
  | var _, h => by simp [closed] at h
  | app f x, h => by
    intro y hy
    simp [args] at hy
    rcases hy with hy | hy
    · exact closed_args f h.1 y hy
    · subst hy; exact h.2

theorem occ_closed (n : Nat) : ∀ t : T, closed t → occ n t = 0
  | S, _ => rfl
  | var _, h => by simp [closed] at h
  | app f x, h => by simp [occ, occ_closed n f h.1, occ_closed n x h.2]

theorem occL_closed (n : Nat) : ∀ C : List T, (∀ x ∈ C, closed x) → occL n C = 0
  | [], _ => rfl
  | x :: xs, h => by
    simp [occL, occ_closed n x (h x (by simp)), occL_closed n xs (fun y hy => h y (by simp [hy]))]

/-- a list is stuck if it has at least three elements and an atom-headed front -/
def stuck : List T → Prop
  | a :: _ :: _ :: _ => head a ≠ S
  | _ => False

section OC1
variable (u v r : Nat) (huv : u ≠ v) (hvr : v ≠ r)

/-- the invariant: a nonempty closed prefix above [v, u.v, r], or already >= 3 occurrences of v -/
def OInv (L : List T) : Prop :=
  (∃ C : List T, C ≠ [] ∧ (∀ x ∈ C, closed x) ∧ L = C ++ [var v, app (var u) (var v), var r]) ∨ 3 ≤ occL v L

include huv hvr in
theorem occ_base : occL v [var v, app (var u) (var v), var r] = 2 := by
  have h1 : (if u = v then 1 else 0) = 0 := by simp [huv]
  have h2 : (if r = v then 1 else 0) = 0 := by simp [Ne.symm hvr]
  simp [occL, occ, h1, h2]

include huv hvr in
theorem inv_step (L L' : List T) (hI : OInv u v r L) (hs : step L = some L') : OInv u v r L' := by
  rcases hI with ⟨C, hC, hcl, rfl⟩ | h3
  · -- closed prefix case
    match C, hC, hcl, hs with
    | [c1], _, hcl, hs =>
      -- [c1, v, u.v, r] -> args c1 ++ [u.v, v.(u.v), r]
      right
      simp only [List.cons_append, List.nil_append, step] at hs
      have hh : head c1 = S := closed_head c1 (hcl c1 (by simp))
      simp [hh] at hs; subst hs
      rw [occL_append, occL_closed v (args c1) (closed_args c1 (hcl c1 (by simp)))]
      have h1 : (if u = v then 1 else 0) = 0 := by simp [huv]
      have h2 : (if r = v then 1 else 0) = 0 := by simp [Ne.symm hvr]
      simp [occL, occ, h1, h2]
    | [c1, c2], _, hcl, hs =>
      right
      simp only [List.cons_append, List.nil_append, step] at hs
      have hh : head c1 = S := closed_head c1 (hcl c1 (by simp))
      simp [hh] at hs; subst hs
      rw [occL_append, occL_closed v (args c1) (closed_args c1 (hcl c1 (by simp)))]
      have h1 : (if u = v then 1 else 0) = 0 := by simp [huv]
      have h2 : (if r = v then 1 else 0) = 0 := by simp [Ne.symm hvr]
      simp [occL, occ, h1, h2, occ_closed v c2 (hcl c2 (by simp))]
    | c1 :: c2 :: c3 :: C', _, hcl, hs =>
      left
      simp only [List.cons_append, step] at hs
      have hh : head c1 = S := closed_head c1 (hcl c1 (by simp))
      simp [hh] at hs; subst hs
      refine ⟨args c1 ++ c3 :: app c2 c3 :: C', by simp, ?_, by simp⟩
      intro x hx
      simp at hx
      rcases hx with hx | hx | hx | hx
      · exact closed_args c1 (hcl c1 (by simp)) x hx
      · rw [hx]; exact hcl c3 (by simp)
      · rw [hx]; exact ⟨hcl c2 (by simp), hcl c3 (by simp)⟩
      · exact hcl x (by simp [hx])
  · right; exact Nat.le_trans h3 (occL_step_ge v L L' hs)

include huv hvr in
theorem inv_run : ∀ (k : Nat) (L L' : List T), OInv u v r L → run k L = some L' → OInv u v r L'
  | 0, L, L', hI, h => by simp [run] at h; subst h; exact hI
  | k + 1, L, L', hI, h => by
    simp only [run] at h
    split at h
    · rename_i L1 hs
      exact inv_run k L1 L' (inv_step u v r huv hvr L L1 hI hs) h
    · exact absurd h (by simp)

/-- in the closed-prefix form the front is closed, hence not stuck -/
theorem not_stuck_prefix (C : List T) (hC : C ≠ []) (hcl : ∀ x ∈ C, closed x) :
    ¬ stuck (C ++ [var v, app (var u) (var v), var r]) := by
  match C, hC with
  | c :: C', _ =>
    have hh : head c = S := closed_head c (hcl c (by simp))
    match C' with
    | [] => simp [stuck, hh]
    | [d] => simp [stuck, hh]
    | d :: e :: C'' => simp [stuck, hh]

include huv hvr in
/-- Corollary OC1 -/
theorem oc1 (Tc : T) (hT : closed Tc) (hne : args Tc ≠ []) (k : Nat) (L : List T)
    (hrun : run k (args Tc ++ [var v, app (var u) (var v), var r]) = some L) (hst : stuck L) :
    3 ≤ occL v L := by
  have h0 : OInv u v r (args Tc ++ [var v, app (var u) (var v), var r]) :=
    Or.inl ⟨args Tc, hne, closed_args Tc hT, rfl⟩
  rcases inv_run u v r huv hvr k _ L h0 hrun with ⟨C, hC, hcl, rfl⟩ | h3
  · exact absurd hst (not_stuck_prefix u v r C hC hcl)
  · exact h3

/-- the first step of [T, u, v, r] is the opening of T -/
theorem first_step (Tc : T) (hT : closed Tc) :
    step [Tc, var u, var v, var r] = some (args Tc ++ [var v, app (var u) (var v), var r]) := by
  simp [step, closed_head Tc hT]

/-- the 'transparent' rule shape has exactly two occurrences of v -/
def wrap : T → List T → T
  | h, [] => h
  | h, w :: ws => wrap (app h w) ws

theorem occ_wrap (n : Nat) : ∀ (h : T) (ws : List T), occ n (wrap h ws) = occ n h + occL n ws
  | h, [] => by simp [wrap, occL]
  | h, w :: ws => by simp [wrap, occ_wrap n (app h w) ws, occ, occL]; omega

include huv hvr in
/-- no closed T != S has a stuck rule [v.w..., (u.v).w'..., rest...] with w, w', rest closed -/
theorem no_transparent (Tc : T) (hT : closed Tc) (hne : args Tc ≠ []) (k : Nat)
    (ws ws' rest : List T) (hw : ∀ x ∈ ws, closed x) (hw' : ∀ x ∈ ws', closed x)
    (hrest : ∀ x ∈ rest, closed x)
    (hrun : run k (args Tc ++ [var v, app (var u) (var v), var r]) =
        some (wrap (var v) ws :: wrap (app (var u) (var v)) ws' :: rest ++ [var r])) : False := by
  have hst : stuck (wrap (var v) ws :: wrap (app (var u) (var v)) ws' :: rest ++ [var r]) := by
    have : head (wrap (var v) ws) = var v := by
      clear hrun hw
      induction ws generalizing u with
      | nil => rfl
      | cons w ws ih =>
        show head (wrap (app (var v) w) ws) = var v
        have : ∀ (h : T) (ws : List T), head (wrap h ws) = head h := by
          intro h ws
          induction ws generalizing h with
          | nil => rfl
          | cons w' ws' ih' => simp [wrap, ih', head]
        rw [this]; rfl
    cases rest with
    | nil => simp [stuck, this]
    | cons x xs => simp [stuck, this]
  have h3 := oc1 u v r huv hvr Tc hT hne k _ hrun hst
  have h1 : (if u = v then 1 else 0) = 0 := by simp [huv]
  have h2 : (if r = v then 1 else 0) = 0 := by simp [Ne.symm hvr]
  rw [show wrap (var v) ws :: wrap (app (var u) (var v)) ws' :: rest ++ [var r] =
      wrap (var v) ws :: wrap (app (var u) (var v)) ws' :: (rest ++ [var r]) by rfl] at h3
  simp [occL, occ_wrap, occ, h1, occL_closed v ws hw, occL_closed v ws' hw', occL_append,
    occL_closed v rest hrest, h2] at h3

end OC1
