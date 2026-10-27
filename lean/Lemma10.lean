/-
  Lemma 10 (no junk-free rotation) — machine-checked (main agent, 2026-10-27). Plain Lean 4 core, no Mathlib.
  Framework: the head machine with opaque atoms (as in lean/BarrierJ.lean): [a, b, c] ++ R => args a ++ [c, b·c] ++ R
  when a has head S; an atom-headed front is stuck, so the run never opens a variable-headed element.
  Two data atoms: x = var 0 and y = var 1, the x-datum above the y-datum.
  * `inv_step`, `inv_run`: the invariant of the hand proof (PROOF.md, Lemma 10) is preserved:
      J1  no list element containing y lies above an element that contains x but not y;
      J2  inside every S-headed subterm, no spine argument containing y precedes one that contains x but not y;
      K   every y-headed subterm that contains x contains y at least twice.
  * `lemma10`: if the run starts from (A ++ X :: B) ++ Y :: C, where A, B, C are free of x and y, X is free of y and
    Y is free of x, then in every reachable list every y-headed subterm containing x contains y at least twice.
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

/-- contains x = var 0 -/
def hx : T → Bool
  | S => false
  | var n => n == 0
  | app f a => hx f || hx a

/-- contains y = var 1 -/
def hy : T → Bool
  | S => false
  | var n => n == 1
  | app f a => hy f || hy a

/-- number of occurrences of y -/
def cy : T → Nat
  | S => 0
  | var n => if n = 1 then 1 else 0
  | app f a => cy f + cy a

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

/-- x-only: contains x but not y -/
def xo (t : T) : Bool := hx t && !hy t

/-- J1: no element containing y lies above an x-only element -/
def J1 : List T → Prop
  | [] => True
  | e :: R => (hy e = true → ∀ f ∈ R, xo f = false) ∧ J1 R

/-- J2: inside every S-headed subterm, no spine argument containing y precedes an x-only spine argument -/
def J2 : T → Prop
  | S => True
  | var _ => True
  | app f a => J2 f ∧ J2 a ∧ (head f = S → J1 (args f ++ [a]))

/-- K: every y-headed subterm containing x contains y at least twice -/
def Kt : T → Prop
  | S => True
  | var _ => True
  | app f a => Kt f ∧ Kt a ∧ (head f = var 1 → hx (app f a) = true → 2 ≤ cy (app f a))

def LInv (L : List T) : Prop := J1 L ∧ (∀ e ∈ L, J2 e) ∧ (∀ e ∈ L, Kt e)

theorem J1_append : ∀ (A B : List T),
    J1 (A ++ B) ↔ J1 A ∧ J1 B ∧ (∀ e ∈ A, hy e = true → ∀ f ∈ B, xo f = false)
  | [], B => by simp [J1]
  | e :: A, B => by
    have ih := J1_append A B
    simp only [List.cons_append, J1]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨h2a, h2b, h2c⟩ := ih.1 h2
      refine ⟨⟨fun he f hf => h1 he f (List.mem_append.2 (Or.inl hf)), h2a⟩, h2b, ?_⟩
      intro e' he' hy' f hf
      rcases List.mem_cons.1 he' with rfl | he'
      · exact h1 hy' f (List.mem_append.2 (Or.inr hf))
      · exact h2c e' he' hy' f hf
    · intro h
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
      refine ⟨?_, ih.2 ⟨h2, h3, fun e' he' => h4 e' (List.mem_cons_of_mem e he')⟩⟩
      intro he f hf
      rcases List.mem_append.1 hf with hf | hf
      · exact h1 he f hf
      · exact h4 e (List.mem_cons_self) he f hf

theorem args_hy : ∀ (a e : T), e ∈ args a → hy e = true → hy a = true
  | S, e, h, _ => by simp [args] at h
  | var _, e, h, _ => by simp [args] at h
  | app f x, e, h, he => by
    simp only [args, List.mem_append, List.mem_singleton] at h
    simp only [hy, Bool.or_eq_true]
    rcases h with h | rfl
    · exact Or.inl (args_hy f e h he)
    · exact Or.inr he

theorem args_hx : ∀ (a e : T), e ∈ args a → hx e = true → hx a = true
  | S, e, h, _ => by simp [args] at h
  | var _, e, h, _ => by simp [args] at h
  | app f x, e, h, he => by
    simp only [args, List.mem_append, List.mem_singleton] at h
    simp only [hx, Bool.or_eq_true]
    rcases h with h | rfl
    · exact Or.inl (args_hx f e h he)
    · exact Or.inr he

theorem args_J2 : ∀ (a e : T), J2 a → e ∈ args a → J2 e
  | S, e, _, h => by simp [args] at h
  | var _, e, _, h => by simp [args] at h
  | app f x, e, hJ, h => by
    simp only [J2] at hJ
    simp only [args, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact args_J2 f e hJ.1 h
    · exact hJ.2.1

theorem args_Kt : ∀ (a e : T), Kt a → e ∈ args a → Kt e
  | S, e, _, h => by simp [args] at h
  | var _, e, _, h => by simp [args] at h
  | app f x, e, hK, h => by
    simp only [Kt] at hK
    simp only [args, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact args_Kt f e hK.1 h
    · exact hK.2.1

theorem J2_J1args : ∀ a : T, J2 a → head a = S → J1 (args a)
  | S, _, _ => by simp [args, J1]
  | var _, _, h => by simp [head] at h
  | app f x, hJ, hh => by
    simp only [J2] at hJ
    simp only [head] at hh
    simp only [args]
    exact hJ.2.2 hh

theorem head_hy : ∀ t : T, head t = var 1 → hy t = true
  | S, h => by simp [head] at h
  | var n, h => by simp [head] at h; subst h; simp [hy]
  | app f _, h => by simp only [head] at h; simp [hy, head_hy f h]

theorem head_cy : ∀ t : T, head t = var 1 → 1 ≤ cy t
  | S, h => by simp [head] at h
  | var n, h => by simp [head] at h; subst h; simp [cy]
  | app f a, h => by simp only [head] at h; have := head_cy f h; simp only [cy]; omega

theorem hy_cy : ∀ t : T, hy t = true → 1 ≤ cy t
  | S, h => by simp [hy] at h
  | var n, h => by simp [hy] at h; subst h; simp [cy]
  | app f a, h => by
    simp only [hy, Bool.or_eq_true] at h
    simp only [cy]
    rcases h with h | h
    · have := hy_cy f h; omega
    · have := hy_cy a h; omega

theorem Kt_self : ∀ t : T, Kt t → head t = var 1 → hx t = true → 2 ≤ cy t
  | S, _, h, _ => by simp [head] at h
  | var n, _, h, h' => by simp [head] at h; subst h; simp [hx] at h'
  | app f a, hK, hh, h' => by
    simp only [Kt] at hK
    simp only [head] at hh
    exact hK.2.2 hh h'

theorem xo_app (b c : T) (hb : xo b = false) (hc : xo c = false) : xo (app b c) = false := by
  unfold xo at *
  simp only [hx, hy]
  cases h1 : hx b <;> cases h2 : hy b <;> cases h3 : hx c <;> cases h4 : hy c <;> simp_all

/-- one head step preserves the invariant -/
theorem inv_step (a b c : T) (R : List T) (ha : head a = S) (h : LInv (a :: b :: c :: R)) :
    LInv (args a ++ c :: app b c :: R) := by
  obtain ⟨hJ1, hJ2, hK⟩ := h
  simp only [J1] at hJ1
  obtain ⟨hA, hB, hC, hR⟩ := hJ1
  have J2a := hJ2 a (by simp)
  have J2b := hJ2 b (by simp)
  have J2c := hJ2 c (by simp)
  have Ka := hK a (by simp)
  have Kb := hK b (by simp)
  have Kc := hK c (by simp)
  refine ⟨?_, ?_, ?_⟩
  · rw [J1_append]
    refine ⟨J2_J1args a J2a ha, ?_, ?_⟩
    · simp only [J1]
      refine ⟨?_, ?_, hR⟩
      · intro hc f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · unfold xo; simp [hy, hc]
        · exact hC hc f hf
      · intro hbc f hf
        simp only [hy, Bool.or_eq_true] at hbc
        rcases hbc with hb | hc
        · exact hB hb f (List.mem_cons_of_mem c hf)
        · exact hC hc f hf
    · intro e he hye f hf
      have h1 := hA (args_hy a e he hye)
      have xb : xo b = false := h1 b (by simp)
      have xc : xo c = false := h1 c (by simp)
      rcases List.mem_cons.1 hf with rfl | hf
      · exact xc
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact xo_app b c xb xc
        · exact h1 f (by simp [hf])
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact args_J2 a e J2a he
    · rcases List.mem_cons.1 he with rfl | he
      · exact J2c
      · rcases List.mem_cons.1 he with rfl | he
        · simp only [J2]
          refine ⟨J2b, J2c, ?_⟩
          intro hb
          rw [J1_append]
          refine ⟨J2_J1args b J2b hb, by simp [J1], ?_⟩
          intro e' he' hye f hf
          rw [List.mem_singleton] at hf
          rw [hf]
          exact hB (args_hy b e' he' hye) c (by simp)
        · exact hJ2 e (by simp [he])
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact args_Kt a e Ka he
    · rcases List.mem_cons.1 he with rfl | he
      · exact Kc
      · rcases List.mem_cons.1 he with rfl | he
        · simp only [Kt]
          refine ⟨Kb, Kc, ?_⟩
          intro hb hxbc
          simp only [hx, Bool.or_eq_true] at hxbc
          simp only [cy]
          have c1 := head_cy b hb
          rcases hxbc with hxb | hxc
          · have := Kt_self b Kb hb hxb; omega
          · cases hyc : hy c
            · have hyb := head_hy b hb
              have := hB hyb c (by simp)
              unfold xo at this
              simp [hxc, hyc] at this
            · have := hy_cy c hyc; omega
        · exact hK e (by simp [he])

theorem inv_step' (L L1 : List T) (h : LInv L) (hs : step L = some L1) : LInv L1 := by
  match L, h, hs with
  | a :: b :: c :: R, h, hs =>
    simp only [step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs; exact inv_step a b c R (by assumption) h
    · simp at hs

theorem inv_run : ∀ (n : Nat) (L L' : List T), LInv L → run n L = some L' → LInv L'
  | 0, L, L', h, hr => by simp [run] at hr; subst hr; exact h
  | n + 1, L, L', h, hr => by
    simp only [run] at hr
    cases hs : step L with
    | none => rw [hs] at hr; simp at hr
    | some L1 => rw [hs] at hr; exact inv_run n L1 L' (inv_step' L L1 h hs) hr

/-! ## The start configuration -/

theorem J1_noy : ∀ L : List T, (∀ e ∈ L, hy e = false) → J1 L
  | [], _ => trivial
  | e :: R, h => by
    simp only [J1]
    refine ⟨fun he => ?_, J1_noy R (fun f hf => h f (List.mem_cons_of_mem e hf))⟩
    rw [h e List.mem_cons_self] at he
    exact absurd he (by decide)

theorem J1_nox : ∀ L : List T, (∀ e ∈ L, hx e = false) → J1 L
  | [], _ => trivial
  | e :: R, h => by
    simp only [J1]
    refine ⟨fun _ f hf => ?_, J1_nox R (fun f hf => h f (List.mem_cons_of_mem e hf))⟩
    have := h f (List.mem_cons_of_mem e hf)
    unfold xo; simp [this]

theorem J2_noy : ∀ t : T, hy t = false → J2 t
  | S, _ => trivial
  | var _, _ => trivial
  | app f a, h => by
    simp only [hy, Bool.or_eq_false_iff] at h
    simp only [J2]
    refine ⟨J2_noy f h.1, J2_noy a h.2, fun _ => J1_noy _ ?_⟩
    intro e he
    rcases List.mem_append.1 he with he | he
    · cases hye : hy e
      · rfl
      · have := args_hy f e he hye; rw [h.1] at this; exact absurd this (by decide)
    · rw [List.mem_singleton] at he; subst he; exact h.2

theorem J2_nox : ∀ t : T, hx t = false → J2 t
  | S, _ => trivial
  | var _, _ => trivial
  | app f a, h => by
    simp only [hx, Bool.or_eq_false_iff] at h
    simp only [J2]
    refine ⟨J2_nox f h.1, J2_nox a h.2, fun _ => J1_nox _ ?_⟩
    intro e he
    rcases List.mem_append.1 he with he | he
    · cases hxe : hx e
      · rfl
      · have := args_hx f e he hxe; rw [h.1] at this; exact absurd this (by decide)
    · rw [List.mem_singleton] at he; subst he; exact h.2

theorem Kt_nox : ∀ t : T, hx t = false → Kt t
  | S, _ => trivial
  | var _, _ => trivial
  | app f a, h => by
    simp only [hx, Bool.or_eq_false_iff] at h
    simp only [Kt]
    refine ⟨Kt_nox f h.1, Kt_nox a h.2, fun _ hh => ?_⟩
    simp [hx, h.1, h.2] at hh

theorem Kt_noy : ∀ t : T, hy t = false → Kt t
  | S, _ => trivial
  | var _, _ => trivial
  | app f a, h => by
    simp only [hy, Bool.or_eq_false_iff] at h
    simp only [Kt]
    refine ⟨Kt_noy f h.1, Kt_noy a h.2, fun hh _ => ?_⟩
    have := head_hy f hh
    rw [h.1] at this
    exact absurd this (by decide)

/-- the start: elements free of x and y (A, B, C), an x-datum X (free of y) above a y-datum Y (free of x) -/
theorem inv_start (A B C : List T) (X Y : T)
    (hA : ∀ e ∈ A, hx e = false ∧ hy e = false) (hB : ∀ e ∈ B, hx e = false ∧ hy e = false)
    (hC : ∀ e ∈ C, hx e = false ∧ hy e = false) (hX : hy X = false) (hY : hx Y = false) :
    LInv ((A ++ X :: B) ++ (Y :: C)) := by
  have hP : ∀ e ∈ A ++ X :: B, hy e = false := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact (hA e he).2
    · rcases List.mem_cons.1 he with rfl | he
      · exact hX
      · exact (hB e he).2
  refine ⟨?_, ?_, ?_⟩
  · rw [J1_append]
    refine ⟨J1_noy _ hP, ?_, ?_⟩
    · simp only [J1]
      refine ⟨fun _ f hf => ?_, J1_noy C (fun f hf => (hC f hf).2)⟩
      unfold xo; simp [(hC f hf).1]
    · intro e he hye
      rw [hP e he] at hye
      exact absurd hye (by decide)
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact J2_noy e (hP e he)
    · rcases List.mem_cons.1 he with rfl | he
      · exact J2_nox _ hY
      · exact J2_noy e (hC e he).2
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact Kt_noy e (hP e he)
    · rcases List.mem_cons.1 he with rfl | he
      · exact Kt_nox _ hY
      · exact Kt_noy e (hC e he).2

/-- subterm relation -/
inductive SubT : T → T → Prop
  | refl (t : T) : SubT t t
  | left {s f a : T} : SubT s f → SubT s (app f a)
  | right {s f a : T} : SubT s a → SubT s (app f a)

theorem Kt_sub (s t : T) (hs : SubT s t) : Kt t → head s = var 1 → hx s = true → 2 ≤ cy s := by
  induction hs with
  | refl => exact Kt_self _
  | left _ ih => intro hK; simp only [Kt] at hK; exact ih hK.1
  | right _ ih => intro hK; simp only [Kt] at hK; exact ih hK.2.1

/-- **Lemma 10** (no junk-free rotation). Start from elements free of x and y, an x-datum X above a y-datum Y. In every
    reachable list, every y-headed subterm (of any element) that contains x contains y at least twice: the bottom datum
    can be brought in front of the other only together with a second copy of itself. -/
theorem lemma10 (A B C : List T) (X Y : T)
    (hA : ∀ e ∈ A, hx e = false ∧ hy e = false) (hB : ∀ e ∈ B, hx e = false ∧ hy e = false)
    (hC : ∀ e ∈ C, hx e = false ∧ hy e = false) (hX : hy X = false) (hY : hx Y = false)
    (n : Nat) (L : List T) (hr : run n ((A ++ X :: B) ++ (Y :: C)) = some L)
    (e : T) (he : e ∈ L) (s : T) (hs : SubT s e) (hsy : head s = var 1) (hsx : hx s = true) : 2 ≤ cy s :=
  Kt_sub s e hs ((inv_run n _ L (inv_start A B C X Y hA hB hC hX hY) hr).2.2 e he) hsy hsx

#print axioms lemma10
#print axioms inv_step
