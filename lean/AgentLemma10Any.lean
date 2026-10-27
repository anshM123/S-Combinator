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

/-! ## Lemma 10 under EVERY evaluation order (agent_work_P, parallel-universality agent, 2026-10-27)

The invariant of Lemma 10, read on whole terms (`J2 t ∧ Kt t`; for t = S e1 ... em, J2 t contains J1 of the list
[e1, ..., em]), is preserved by EVERY single reduction step S x y z → x z (y z), wherever the redex is: a head step
(`hstep_inv`, the list step of Lemma 10, now also allowing a variable-headed x) or a step inside a spine argument.
Hence Lemma 10 holds for every evaluation order and in the multiway system (`lemma10_any`): in every term reachable
from the start by ANY reduction sequence — in particular after any number of ReplaceAll passes (`redstar_passN`) —
every y-headed subterm that contains x contains y at least twice.
-/

inductive Red : T → T → Prop
  | redex (x y z : T) : Red (app (app (app S x) y) z) (app (app x z) (app y z))
  | left {f f' : T} (a : T) : Red f f' → Red (app f a) (app f' a)
  | right (f : T) {a a' : T} : Red a a' → Red (app f a) (app f a')

inductive RedStar : T → T → Prop
  | refl (t : T) : RedStar t t
  | tail {t u v : T} : RedStar t u → Red u v → RedStar t v

theorem RedStar.trans' {t u v : T} (h1 : RedStar t u) (h2 : RedStar u v) : RedStar t v := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact RedStar.tail ih h

theorem redstar_left' {f f' : T} (a : T) (h : RedStar f f') : RedStar (app f a) (app f' a) := by
  induction h with
  | refl => exact RedStar.refl _
  | tail _ h ih => exact RedStar.tail ih (Red.left a h)

theorem redstar_right' (f : T) {a a' : T} (h : RedStar a a') : RedStar (app f a) (app f a') := by
  induction h with
  | refl => exact RedStar.refl _
  | tail _ h ih => exact RedStar.tail ih (Red.right f h)

inductive HStep : T → T → Prop
  | redex (x y z : T) : HStep (app (app (app S x) y) z) (app (app x z) (app y z))
  | left {f f' : T} (a : T) : HStep f f' → HStep (app f a) (app f' a)

theorem hstep_red {t u : T} (h : HStep t u) : Red t u := by
  induction h with
  | redex x y z => exact Red.redex x y z
  | left a _ ih => exact Red.left a ih

/-- reduction neither creates nor erases variables, and never lowers the number of y's -/
theorem red_vars {t u : T} (h : Red t u) : hx u = hx t ∧ hy u = hy t ∧ cy t ≤ cy u := by
  induction h with
  | redex x y z =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [hx]
      generalize hx x = a
      generalize hx y = b
      generalize hx z = c
      cases a <;> cases b <;> cases c <;> rfl
    · simp only [hy]
      generalize hy x = a
      generalize hy y = b
      generalize hy z = c
      cases a <;> cases b <;> cases c <;> rfl
    · simp only [cy]; omega
  | left a _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [hx, ih.1]
    · simp only [hy, ih.2.1]
    · simp only [cy]; have := ih.2.2; omega
  | right f _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [hx, ih.1]
    · simp only [hy, ih.2.1]
    · simp only [cy]; have := ih.2.2; omega

/-- the (contains x, contains y) signature -/
def sig (e : T) : Bool × Bool := (hx e, hy e)

theorem xo_sig {e f : T} (h : sig e = sig f) : xo e = xo f := by
  simp only [sig, Prod.mk.injEq] at h
  unfold xo
  rw [h.1, h.2]

theorem J1_congr : ∀ (L L' : List T), L.map sig = L'.map sig → J1 L → J1 L'
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | e :: L, e' :: L', h, hJ => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [J1] at hJ ⊢
    refine ⟨?_, J1_congr L L' h.2 hJ.2⟩
    intro hy' f' hf'
    have hye : hy e = true := by
      have := h.1
      simp only [sig, Prod.mk.injEq] at this
      rw [this.2]; exact hy'
    have hmem : sig f' ∈ L.map sig := by rw [h.2]; exact List.mem_map_of_mem hf'
    obtain ⟨f, hf, hs⟩ := List.mem_map.1 hmem
    rw [← xo_sig hs]
    exact hJ.1 hye f hf

/-- every step is a head step, or keeps the head and the signatures of the spine arguments -/
theorem red_cases {f f' : T} (h : Red f f') :
    HStep f f' ∨ (head f' = head f ∧ (args f).map sig = (args f').map sig) := by
  induction h with
  | redex x y z => exact Or.inl (HStep.redex x y z)
  | left a hr ih =>
    rcases ih with hs | ⟨e, m⟩
    · exact Or.inl (HStep.left a hs)
    · refine Or.inr ⟨?_, ?_⟩
      · simp only [head]; exact e
      · simp only [args, List.map_append, m]
  | right g hr =>
    refine Or.inr ⟨rfl, ?_⟩
    have hv := red_vars hr
    simp only [args, List.map_append, List.map_cons, List.map_nil, sig, hv.1, hv.2.1]

theorem hstep_args {t u : T} (h : HStep t u) : ∃ x y z R, args t = x :: y :: z :: R ∧ head t = S ∧
    args u = args x ++ z :: app y z :: R ∧ head u = head x := by
  induction h with
  | redex x y z =>
    refine ⟨x, y, z, [], ?_, rfl, ?_, rfl⟩
    · simp [args]
    · simp [args]
  | left a _ ih =>
    obtain ⟨x, y, z, R, h1, h2, h3, h4⟩ := ih
    refine ⟨x, y, z, R ++ [a], ?_, ?_, ?_, ?_⟩
    · simp only [args, h1]; simp
    · simp only [head]; exact h2
    · simp only [args, h3]; simp
    · simp only [head]; exact h4

def sumcy : List T → Nat
  | [] => 0
  | e :: L => cy e + sumcy L

theorem sumcy_append : ∀ (A B : List T), sumcy (A ++ B) = sumcy A + sumcy B
  | [], B => by simp [sumcy]
  | e :: A, B => by simp only [List.cons_append, sumcy, sumcy_append A B]; omega

theorem sumcy_le : ∀ t : T, sumcy (args t) ≤ cy t
  | S => by simp [args, sumcy]
  | var _ => by simp [args, sumcy]
  | app f a => by
    simp only [args, sumcy_append, sumcy, cy]
    have := sumcy_le f
    omega

theorem sumcy_mem : ∀ (L : List T) (e : T), e ∈ L → cy e ≤ sumcy L
  | [], e, h => by simp at h
  | f :: L, e, h => by
    simp only [sumcy]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := sumcy_mem L e h; omega

theorem hy_of_xo {e : T} (h1 : xo e = false) (h2 : hx e = true) : hy e = true := by
  unfold xo at h1
  cases hh : hy e
  · simp [h2, hh] at h1
  · rfl

theorem hx_args : ∀ t : T, head t = S → hx t = true → ∃ e ∈ args t, hx e = true
  | S, _, h => by simp [hx] at h
  | var n, h, _ => by simp [head] at h
  | app f a, hS, h => by
    simp only [hx, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨e, he, hxe⟩ := hx_args f hS h
      exact ⟨e, by simp [args, he], hxe⟩
    · exact ⟨a, by simp [args], h⟩

/-- the K step: if the first list element x is y-headed and some element of the list contains x, then the list has at
    least two y's (J1 forces an x-carrier below x to carry y too) -/
theorem K_list (x : T) (L : List T) (hJ : J1 (x :: L)) (hKx : Kt x) (hxh : head x = var 1)
    (hxs : hx x = true ∨ ∃ e ∈ L, hx e = true) : 2 ≤ sumcy (x :: L) := by
  simp only [sumcy]
  rcases hxs with hxx | ⟨e, he, hxe⟩
  · have := Kt_self x hKx hxh hxx; omega
  · have hJ' : (hy x = true → ∀ f ∈ L, xo f = false) ∧ J1 L := hJ
    have hye := hy_of_xo (hJ'.1 (head_hy x hxh) e he) hxe
    have h1 := hy_cy e hye
    have h2 := sumcy_mem L e he
    have h3 := head_cy x hxh
    omega

theorem J1_prefix (A B : List T) (h : J1 (A ++ B)) : J1 A := ((J1_append A B).1 h).1

theorem J1_single (z : T) : J1 [z] := by simp [J1]

/-- one head step anywhere in a spine preserves the term invariant -/
theorem hstep_inv {t u : T} (h : HStep t u) : J2 t → Kt t → J2 u ∧ Kt u := by
  induction h with
  | redex x y z =>
    intro hJ hK
    have hJ' : J2 (app (app S x) y) ∧ J2 z ∧ (head (app (app S x) y) = S → J1 (args (app (app S x) y) ++ [z])) := hJ
    obtain ⟨hJSxy, Jz, hJ3⟩ := hJ'
    have hJSxy' : J2 (app S x) ∧ J2 y ∧ (head (app S x) = S → J1 (args (app S x) ++ [y])) := hJSxy
    obtain ⟨hJSx, Jy, _⟩ := hJSxy'
    have hJSx' : J2 S ∧ J2 x ∧ (head S = S → J1 (args S ++ [x])) := hJSx
    obtain ⟨_, Jx, _⟩ := hJSx'
    have J1xyz : J1 [x, y, z] := hJ3 rfl
    have hK' : Kt (app (app S x) y) ∧ Kt z ∧
        (head (app (app S x) y) = var 1 → hx (app (app (app S x) y) z) = true →
          2 ≤ cy (app (app (app S x) y) z)) := hK
    obtain ⟨hKSxy, Kz, _⟩ := hK'
    have hKSxy' : Kt (app S x) ∧ Kt y ∧
        (head (app S x) = var 1 → hx (app (app S x) y) = true → 2 ≤ cy (app (app S x) y)) := hKSxy
    obtain ⟨hKSx, Ky, _⟩ := hKSxy'
    have hKSx' : Kt S ∧ Kt x ∧ (head S = var 1 → hx (app S x) = true → 2 ≤ cy (app S x)) := hKSx
    obtain ⟨_, Kx, _⟩ := hKSx'
    have J1a : hy x = true → ∀ f ∈ [y, z], xo f = false := J1xyz.1
    have J1b : hy y = true → ∀ f ∈ [z], xo f = false := J1xyz.2.1
    have LI : LInv [x, y, z] := by
      refine ⟨J1xyz, ?_, ?_⟩
      · intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> assumption
      · intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> assumption
    have Jyz : J2 (app y z) := by
      show J2 y ∧ J2 z ∧ (head y = S → J1 (args y ++ [z]))
      refine ⟨Jy, Jz, fun hyS => ?_⟩
      rw [J1_append]
      refine ⟨J2_J1args y Jy hyS, J1_single z, ?_⟩
      intro e he hye f hf
      exact J1b (args_hy y e he hye) f hf
    have hxS : head x = S → J1 ((args x ++ [z]) ++ [app y z]) := fun hS => by
      have := (inv_step x y z [] hS LI).1
      simpa using this
    refine ⟨?_, ?_⟩
    · show (J2 x ∧ J2 z ∧ (head x = S → J1 (args x ++ [z]))) ∧ J2 (app y z) ∧
          (head x = S → J1 ((args x ++ [z]) ++ [app y z]))
      exact ⟨⟨Jx, Jz, fun hS => J1_prefix _ _ (hxS hS)⟩, Jyz, hxS⟩
    · show (Kt x ∧ Kt z ∧ (head x = var 1 → hx (app x z) = true → 2 ≤ cy (app x z))) ∧
          (Kt y ∧ Kt z ∧ (head y = var 1 → hx (app y z) = true → 2 ≤ cy (app y z))) ∧
          (head x = var 1 → hx (app (app x z) (app y z)) = true → 2 ≤ cy (app (app x z) (app y z)))
      refine ⟨⟨Kx, Kz, fun hxh hxs => ?_⟩, ⟨Ky, Kz, fun hyh hxs => ?_⟩, fun hxh hxs => ?_⟩
      · simp only [hx, Bool.or_eq_true] at hxs
        simp only [cy]
        rcases hxs with h1 | h1
        · have := Kt_self x Kx hxh h1; omega
        · have hyz := hy_of_xo (J1a (head_hy x hxh) z (by simp)) h1
          have := hy_cy z hyz; have := head_cy x hxh; omega
      · simp only [hx, Bool.or_eq_true] at hxs
        simp only [cy]
        rcases hxs with h1 | h1
        · have := Kt_self y Ky hyh h1; omega
        · have hyz := hy_of_xo (J1b (head_hy y hyh) z (by simp)) h1
          have := hy_cy z hyz; have := head_cy y hyh; omega
      · simp only [hx, Bool.or_eq_true] at hxs
        simp only [cy]
        have c1 := head_cy x hxh
        rcases hxs with (h1 | h1) | (h1 | h1)
        · have := Kt_self x Kx hxh h1; omega
        · have hyz := hy_of_xo (J1a (head_hy x hxh) z (by simp)) h1
          have := hy_cy z hyz; omega
        · have hyy := hy_of_xo (J1a (head_hy x hxh) y (by simp)) h1
          have := hy_cy y hyy; omega
        · have hyz := hy_of_xo (J1a (head_hy x hxh) z (by simp)) h1
          have := hy_cy z hyz; omega
  | @left f f' a h ih =>
    intro hJ hK
    have hJ' : J2 f ∧ J2 a ∧ (head f = S → J1 (args f ++ [a])) := hJ
    have hK' : Kt f ∧ Kt a ∧ (head f = var 1 → hx (app f a) = true → 2 ≤ cy (app f a)) := hK
    obtain ⟨Jf, Ja, hJ1⟩ := hJ'
    obtain ⟨Kf, Ka, _⟩ := hK'
    obtain ⟨Jf', Kf'⟩ := ih Jf Kf
    obtain ⟨x, y, z, R, h1, h2, h3, h4⟩ := hstep_args h
    have hargs : args (app f a) = x :: y :: z :: (R ++ [a]) := by
      show args f ++ [a] = _
      rw [h1]; simp
    have J1L : J1 (x :: y :: z :: (R ++ [a])) := by
      have := hJ1 h2
      rw [← hargs]; exact this
    have JL : ∀ e ∈ x :: y :: z :: (R ++ [a]), J2 e := fun e he =>
      args_J2 (app f a) e hJ (by rw [hargs]; exact he)
    have KL : ∀ e ∈ x :: y :: z :: (R ++ [a]), Kt e := fun e he =>
      args_Kt (app f a) e hK (by rw [hargs]; exact he)
    have hv := red_vars (hstep_red (HStep.left a h))
    refine ⟨?_, ?_⟩
    · show J2 f' ∧ J2 a ∧ (head f' = S → J1 (args f' ++ [a]))
      refine ⟨Jf', Ja, fun hS => ?_⟩
      rw [h4] at hS
      have := (inv_step x y z (R ++ [a]) hS ⟨J1L, JL, KL⟩).1
      rw [h3]; simpa using this
    · show Kt f' ∧ Kt a ∧ (head f' = var 1 → hx (app f' a) = true → 2 ≤ cy (app f' a))
      refine ⟨Kf', Ka, fun hv1 hxs => ?_⟩
      rw [h4] at hv1
      rw [hv.1] at hxs
      have hSfa : head (app f a) = S := h2
      obtain ⟨e, he, hxe⟩ := hx_args (app f a) hSfa hxs
      rw [hargs] at he
      have hxs' : hx x = true ∨ ∃ e ∈ y :: z :: (R ++ [a]), hx e = true := by
        rcases List.mem_cons.1 he with rfl | he'
        · exact Or.inl hxe
        · exact Or.inr ⟨e, he', hxe⟩
      have k2 := K_list x (y :: z :: (R ++ [a])) J1L (KL x (by simp)) hv1 hxs'
      have h5 := sumcy_le (app f a)
      rw [hargs] at h5
      have := hv.2.2
      omega

/-- every single reduction step, anywhere, preserves the term invariant -/
theorem red_inv {t u : T} (h : Red t u) : J2 t → Kt t → J2 u ∧ Kt u := by
  induction h with
  | redex x y z => exact hstep_inv (HStep.redex x y z)
  | @left f f' a hr ih =>
    intro hJ hK
    rcases red_cases hr with hs | ⟨e, m⟩
    · exact hstep_inv (HStep.left a hs) hJ hK
    · have hJ' : J2 f ∧ J2 a ∧ (head f = S → J1 (args f ++ [a])) := hJ
      have hK' : Kt f ∧ Kt a ∧ (head f = var 1 → hx (app f a) = true → 2 ≤ cy (app f a)) := hK
      obtain ⟨Jf, Ja, hJ1⟩ := hJ'
      obtain ⟨Kf, Ka, hK3⟩ := hK'
      obtain ⟨Jf', Kf'⟩ := ih Jf Kf
      have hv := red_vars (Red.left a hr)
      refine ⟨?_, ?_⟩
      · show J2 f' ∧ J2 a ∧ (head f' = S → J1 (args f' ++ [a]))
        refine ⟨Jf', Ja, fun hS => ?_⟩
        rw [e] at hS
        exact J1_congr _ _ (by simp only [List.map_append, m]) (hJ1 hS)
      · show Kt f' ∧ Kt a ∧ (head f' = var 1 → hx (app f' a) = true → 2 ≤ cy (app f' a))
        refine ⟨Kf', Ka, fun hv1 hxs => ?_⟩
        rw [e] at hv1
        rw [hv.1] at hxs
        have := hK3 hv1 hxs
        have := hv.2.2
        omega
  | @right f a a' hr ih =>
    intro hJ hK
    have hJ' : J2 f ∧ J2 a ∧ (head f = S → J1 (args f ++ [a])) := hJ
    have hK' : Kt f ∧ Kt a ∧ (head f = var 1 → hx (app f a) = true → 2 ≤ cy (app f a)) := hK
    obtain ⟨Jf, Ja, hJ1⟩ := hJ'
    obtain ⟨Kf, Ka, hK3⟩ := hK'
    obtain ⟨Ja', Ka'⟩ := ih Ja Ka
    have hv := red_vars (Red.right f hr)
    have hva := red_vars hr
    refine ⟨?_, ?_⟩
    · show J2 f ∧ J2 a' ∧ (head f = S → J1 (args f ++ [a']))
      refine ⟨Jf, Ja', fun hS => ?_⟩
      exact J1_congr _ _ (by simp [List.map_append, sig, hva.1, hva.2.1]) (hJ1 hS)
    · show Kt f ∧ Kt a' ∧ (head f = var 1 → hx (app f a') = true → 2 ≤ cy (app f a'))
      refine ⟨Kf, Ka', fun hv1 hxs => ?_⟩
      rw [hv.1] at hxs
      have := hK3 hv1 hxs
      have := hv.2.2
      omega

theorem redstar_inv {t u : T} (h : RedStar t u) (hJ : J2 t) (hK : Kt t) : J2 u ∧ Kt u := by
  induction h with
  | refl => exact ⟨hJ, hK⟩
  | tail _ h ih => exact red_inv h ih.1 ih.2

/-- from a list with the list invariant to the term S e1 ... em -/
theorem inv_build : ∀ (L : List T) (u : T), head u = S → J2 u → Kt u → J1 (args u ++ L) →
    (∀ e ∈ L, J2 e) → (∀ e ∈ L, Kt e) → J2 (L.foldl app u) ∧ Kt (L.foldl app u)
  | [], u, _, hJ, hK, _, _, _ => ⟨hJ, hK⟩
  | e :: L, u, hS, hJ, hK, hJ1, hJL, hKL => by
    show J2 (L.foldl app (app u e)) ∧ Kt (L.foldl app (app u e))
    have hJ1' : J1 (args u ++ [e]) := J1_prefix _ L (by simpa using hJ1)
    apply inv_build L (app u e) hS
    · show J2 u ∧ J2 e ∧ (head u = S → J1 (args u ++ [e]))
      exact ⟨hJ, hJL e (by simp), fun _ => hJ1'⟩
    · show Kt u ∧ Kt e ∧ (head u = var 1 → hx (app u e) = true → 2 ≤ cy (app u e))
      refine ⟨hK, hKL e (by simp), fun h1 _ => ?_⟩
      rw [hS] at h1
      exact absurd h1 (by simp)
    · show J1 ((args u ++ [e]) ++ L)
      simpa using hJ1
    · exact fun f hf => hJL f (by simp [hf])
    · exact fun f hf => hKL f (by simp [hf])

/-- one ReplaceAll pass (as in agent_work_P/lean/ParTime.lean) and its being a reduction sequence -/
def pass : T → T
  | S => S
  | var n => var n
  | app (app (app S x) y) a => app (app x a) (app y a)
  | app f a => app (pass f) (pass a)

def passN : Nat → T → T
  | 0, t => t
  | n + 1, t => pass (passN n t)

theorem pass_app (f a : T) (h : ∀ x y, f ≠ app (app S x) y) : pass (app f a) = app (pass f) (pass a) := by
  match f, h with
  | S, _ => rfl
  | var n, _ => rfl
  | app S x, _ => rfl
  | app (var n) x, _ => rfl
  | app (app S x) y, h => exact absurd rfl (h x y)
  | app (app (var n) x) y, _ => rfl
  | app (app (app p q) r) y, _ => rfl

theorem redstar_pass : ∀ t : T, RedStar t (pass t)
  | S => RedStar.refl _
  | var n => RedStar.refl _
  | app f a => by
    by_cases hr : ∃ x y, f = app (app S x) y
    · obtain ⟨x, y, rfl⟩ := hr
      exact RedStar.tail (RedStar.refl _) (Red.redex x y a)
    · have hr' : ∀ x y, f ≠ app (app S x) y := fun x y e => hr ⟨x, y, e⟩
      rw [pass_app f a hr']
      exact (redstar_left' a (redstar_pass f)).trans' (redstar_right' (pass f) (redstar_pass a))

theorem redstar_passN (t : T) : ∀ n : Nat, RedStar t (passN n t)
  | 0 => RedStar.refl t
  | n + 1 => (redstar_passN t n).trans' (redstar_pass (passN n t))

/-- **Lemma 10 under every evaluation order.** Start from the term S A⃗ X B⃗ Y C⃗ (elements of A, B, C free of x and
    y, an x-datum X free of y above a y-datum Y free of x).  In EVERY term u reachable by ANY reduction sequence
    (any evaluation order, the multiway system), every y-headed subterm containing x contains y at least twice. -/
theorem lemma10_any (A B C : List T) (X Y : T)
    (hA : ∀ e ∈ A, hx e = false ∧ hy e = false) (hB : ∀ e ∈ B, hx e = false ∧ hy e = false)
    (hC : ∀ e ∈ C, hx e = false ∧ hy e = false) (hX : hy X = false) (hY : hx Y = false)
    (u : T) (hr : RedStar (((A ++ X :: B) ++ (Y :: C)).foldl app S) u)
    (s : T) (hs : SubT s u) (hsy : head s = var 1) (hsx : hx s = true) : 2 ≤ cy s := by
  obtain ⟨hJ1, hJ2, hK⟩ := inv_start A B C X Y hA hB hC hX hY
  have h0 := inv_build ((A ++ X :: B) ++ (Y :: C)) S rfl trivial trivial (by simpa [args] using hJ1) hJ2 hK
  exact Kt_sub s u hs (redstar_inv hr h0.1 h0.2).2 hsy hsx

/-- the ReplaceAll instance -/
theorem lemma10_replaceAll (A B C : List T) (X Y : T)
    (hA : ∀ e ∈ A, hx e = false ∧ hy e = false) (hB : ∀ e ∈ B, hx e = false ∧ hy e = false)
    (hC : ∀ e ∈ C, hx e = false ∧ hy e = false) (hX : hy X = false) (hY : hx Y = false)
    (n : Nat) (s : T) (hs : SubT s (passN n (((A ++ X :: B) ++ (Y :: C)).foldl app S)))
    (hsy : head s = var 1) (hsx : hx s = true) : 2 ≤ cy s :=
  lemma10_any A B C X Y hA hB hC hX hY _ (redstar_passN _ n) s hs hsy hsx

#print axioms red_inv
#print axioms lemma10_any
#print axioms lemma10_replaceAll
