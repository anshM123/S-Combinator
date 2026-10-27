/-
  Proposition G (pushdown discipline of fork-decrements) — machine-checked (main agent, 2026-10-27). Plain Lean 4 core.
  The head machine [a, b, c] ++ R => args a ++ [c, b·c] ++ R on S-terms with atoms (an atom-headed front is stuck).
  `Gen C t`: t is built by application from subterms of C.
  * `gen_run`: every element of every list reachable from args C is built from subterms of C; in particular every
    component of a head normal form of C (the continuation after a fork-decrement) is. Information created after C was
    built cannot reach the continuation: fork-decrements are last-in-first-out with records fixed at push time.
-/

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

def step : List T → Option (List T)
  | a :: b :: c :: R => if head a = S then some (args a ++ c :: app b c :: R) else none
  | _ => none

def run : Nat → List T → Option (List T)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

inductive SubT : T → T → Prop
  | refl (t : T) : SubT t t
  | left {s f : T} (a : T) : SubT s f → SubT s (app f a)
  | right (f : T) {s a : T} : SubT s a → SubT s (app f a)

theorem sub_trans {r s t : T} (h1 : SubT r s) (h2 : SubT s t) : SubT r t := by
  induction h2 with
  | refl => exact h1
  | left a _ ih => exact SubT.left a (ih h1)
  | right f _ ih => exact SubT.right f (ih h1)

/-- built by application from subterms of C -/
inductive Gen (C : T) : T → Prop
  | sub {t : T} : SubT t C → Gen C t
  | app {f a : T} : Gen C f → Gen C a → Gen C (app f a)

theorem sub_args : ∀ (t e : T), e ∈ args t → SubT e t
  | S, e, h => by simp [args] at h
  | var _, e, h => by simp [args] at h
  | app f x, e, h => by
    simp only [args, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact SubT.left x (sub_args f e h)
    · exact SubT.right f (SubT.refl _)

theorem gen_args (C : T) : ∀ (t e : T), Gen C t → e ∈ args t → Gen C e := by
  intro t e ht he
  induction ht generalizing e with
  | sub hs => exact Gen.sub (sub_trans (sub_args _ e he) hs)
  | @app f a _ ha ihf _ =>
    simp only [args, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ihf e he
    · exact ha

theorem gen_step (C : T) (L L' : List T) (hL : ∀ e ∈ L, Gen C e) (hs : step L = some L') : ∀ e ∈ L', Gen C e := by
  match L, hs with
  | a :: b :: c :: R, hs =>
    simp only [step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs
      subst hs
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact gen_args C a e (hL a (by simp)) he
      rcases List.mem_cons.1 he with rfl | he
      · exact hL _ (by simp)
      rcases List.mem_cons.1 he with rfl | he
      · exact Gen.app (hL b (by simp)) (hL c (by simp))
      · exact hL e (by simp [he])
    · simp at hs

/-- **Proposition G.** Every element of every list reachable from args C — in particular every component of a head
    normal form of C — is built by application from subterms of C. -/
theorem gen_run (C : T) : ∀ (n : Nat) (L : List T), run n (args C) = some L → ∀ e ∈ L, Gen C e := by
  intro n
  suffices h : ∀ (L0 L : List T), (∀ e ∈ L0, Gen C e) → run n L0 = some L → ∀ e ∈ L, Gen C e by
    exact fun L hr => h (args C) L (fun e he => Gen.sub (sub_args C e he)) hr
  induction n with
  | zero => intro L0 L h0 hr; simp [run] at hr; subst hr; exact h0
  | succ n ih =>
    intro L0 L h0 hr
    simp only [run] at hr
    cases hs : step L0 with
    | none => rw [hs] at hr; simp at hr
    | some L1 => rw [hs] at hr; exact ih L1 L (gen_step C L0 L1 h0 hs) hr

#print axioms gen_run
