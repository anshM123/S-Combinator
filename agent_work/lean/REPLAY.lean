/-
  agent_work/lean/REPLAY.lean  (non-universality agent, 2026-10-27).  The replay relation between consecutive
  phases of a Church chain.  Plain Lean 4 core, no Mathlib.
  th w q c : replace every occurrence of the term w by the atom var q, and the live atom var 0 by var c
  (structurally: the outermost occurrences of w are replaced).  A front is *w-prefixed* if some left-spine prefix of
  it equals w.  Replay lemma: one head step commutes with th whenever the front is not w-prefixed and the glued
  node b.c is not w itself.  Corollary (`replay_reexec`): if the generic run of the list args w ++ [w, y, x.y, r]
  (the run of the datum w.w, i.e. what a phase-2 run continues with after producing the self-application w.w)
  reaches a p-headed front (TRANSFER) without a w-prefixed front and without re-creating w, then the generic run of
  the phase-3 datum w[p:=c].q reaches the corresponding c-headed front (REEXEC) — the phase-2 transfer is replayed
  as a re-execution of the frozen value.
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

def size : T → Nat
  | S => 1
  | var _ => 1
  | app f x => size f + size x + 1

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

/-- replace w by var q and the live atom var 0 by var c -/
def th (w : T) (q c : Nat) : T → T
  | S => if S = w then var q else S
  | var n => if var n = w then var q else (if n = 0 then var c else var n)
  | app f x => if app f x = w then var q else app (th w q c f) (th w q c x)

/-- substitution of the live atom only: p := c -/
def sb (c : Nat) : T → T
  | S => S
  | var n => if n = 0 then var c else var n
  | app f x => app (sb c f) (sb c x)

/-- some left-spine prefix equals w -/
def wpre (w : T) : T → Prop
  | S => S = w
  | var n => var n = w
  | app f x => app f x = w ∨ wpre w f

theorem th_args (w : T) (q c : Nat) : ∀ a : T, ¬ wpre w a → args (th w q c a) = (args a).map (th w q c)
  | S, h => by
    have : S ≠ w := fun e => h e
    simp [th, this, args]
  | var n, h => by
    have : var n ≠ w := fun e => h e
    simp only [th, this, ite_false]
    split <;> simp [args]
  | app f x, h => by
    have h1 : app f x ≠ w := fun e => h (Or.inl e)
    have h2 : ¬ wpre w f := fun e => h (Or.inr e)
    simp only [th, h1, ite_false, args]
    rw [th_args w q c f h2]
    simp

theorem th_headS (w : T) (q c : Nat) : ∀ a : T, ¬ wpre w a → head a = S → head (th w q c a) = S
  | S, h, _ => by
    have : S ≠ w := fun e => h e
    simp [th, this, head]
  | var n, _, hS => by simp [head] at hS
  | app f x, h, hS => by
    have h1 : app f x ≠ w := fun e => h (Or.inl e)
    have h2 : ¬ wpre w f := fun e => h (Or.inr e)
    simp only [th, h1, ite_false, head]
    exact th_headS w q c f h2 (by simpa [head] using hS)

theorem th_head0 (w : T) (q c : Nat) : ∀ a : T, ¬ wpre w a → head a = var 0 → head (th w q c a) = var c
  | S, _, hS => by simp [head] at hS
  | var n, h, hS => by
    have : var n ≠ w := fun e => h e
    simp [head] at hS; subst hS
    simp [th, this, head]
  | app f x, h, hS => by
    have h1 : app f x ≠ w := fun e => h (Or.inl e)
    have h2 : ¬ wpre w f := fun e => h (Or.inr e)
    simp only [th, h1, ite_false, head]
    exact th_head0 w q c f h2 (by simpa [head] using hS)

/-- **Replay lemma (one step).** -/
theorem replay_step (w : T) (q c : Nat) (a b d : T) (R : List T) (hS : head a = S) (hG : ¬ wpre w a)
    (hne : app b d ≠ w) :
    step ((a :: b :: d :: R).map (th w q c)) = some ((args a ++ d :: app b d :: R).map (th w q c)) := by
  simp only [List.map_cons, step, th_headS w q c a hG hS, ite_true, th_args w q c a hG, List.map_append]
  simp [th, hne]

/-- the guard: front not w-prefixed and the glued node is not w -/
def G (w : T) : List T → Prop
  | a :: b :: d :: _ => ¬ wpre w a ∧ app b d ≠ w
  | _ => True

def runOK (w : T) : Nat → List T → Prop
  | 0, _ => True
  | k + 1, L => G w L ∧ (match step L with
    | some L' => runOK w k L'
    | none => True)

/-- **Replay lemma (runs).** -/
theorem replay_run (w : T) (q c : Nat) : ∀ (k : Nat) (L L' : List T), runOK w k L → run k L = some L' →
    run k (L.map (th w q c)) = some (L'.map (th w q c))
  | 0, L, L', _, h => by simp [run] at h; subst h; simp [run]
  | k + 1, L, L', hok, h => by
    match L, hok, h with
    | a :: b :: d :: R, hok, h =>
      obtain ⟨⟨hG, hne⟩, hrest⟩ := hok
      simp only [run] at h
      by_cases hS : head a = S
      · have hs : step (a :: b :: d :: R) = some (args a ++ d :: app b d :: R) := by simp [step, hS]
        rw [hs] at h hrest
        simp only at h hrest
        have ih := replay_run w q c k _ L' hrest h
        simp only [run]
        rw [replay_step w q c a b d R hS hG hne]
        exact ih
      · have hs : step (a :: b :: d :: R) = none := by simp [step, hS]
        rw [hs] at h; simp at h
    | [], _, h => simp [run, step] at h
    | [_], _, h => simp [run, step] at h
    | [_, _], _, h => simp [run, step] at h

theorem size_pos : ∀ t : T, 0 < size t
  | S => by simp [size]
  | var _ => by simp [size]
  | app f x => by simp [size]

theorem size_args : ∀ t : T, ∀ s ∈ args t, size s < size t
  | S, s, hs => by simp [args] at hs
  | var _, s, hs => by simp [args] at hs
  | app f x, s, hs => by
    simp [args] at hs
    rcases hs with hs | hs
    · have := size_args f s hs; simp [size]; omega
    · subst hs; have := size_pos f; simp [size]; omega

/-- on terms smaller than w, th is just the substitution p := c -/
theorem th_small (w : T) (q c : Nat) : ∀ t : T, size t < size w → th w q c t = sb c t
  | S, h => by
    have : S ≠ w := fun e => by subst e; simp at h
    simp [th, this, sb]
  | var n, h => by
    have : var n ≠ w := fun e => by subst e; simp at h
    simp [th, this, sb]
  | app f x, h => by
    have h1 : app f x ≠ w := fun e => by subst e; simp at h
    have hf : size f < size w := by simp [size] at h; omega
    have hx : size x < size w := by simp [size] at h; omega
    simp [th, h1, sb, th_small w q c f hf, th_small w q c x hx]

theorem sb_head : ∀ (c : Nat) (t : T), head t = S → head (sb c t) = S
  | _, S, _ => by simp [sb, head]
  | _, var _, h => by simp [head] at h
  | c, app f x, h => by simp only [sb, head]; exact sb_head c f (by simpa [head] using h)

theorem sb_args : ∀ (c : Nat) (t : T), head t = S → args (sb c t) = (args t).map (sb c)
  | _, S, _ => by simp [sb, args]
  | _, var _, h => by simp [head] at h
  | c, app f x, h => by
    simp only [sb, args]
    rw [sb_args c f (by simpa [head] using h)]
    simp

theorem wpre_head (w : T) (hw : head w = S) (n : Nat) : ∀ a : T, head a = var n → ¬ wpre w a
  | S, h, _ => by simp [head] at h
  | var m, h, hp => by simp [wpre] at hp; subst hp; simp [head] at hw
  | app f x, h, hp => by
    rcases hp with hp | hp
    · subst hp; rw [hw] at h; simp at h
    · exact wpre_head w hw n f (by simpa [head] using h) hp

theorem th_self (w : T) (q c : Nat) : th w q c w = var q := by
  cases w <;> simp [th]

/-- **Corollary (replay of a transfer as a re-execution).**  Let w be S-headed.  If the generic run of the list
    args w ++ [w, y, x.y, r] reaches, after k guarded steps, a list whose front is p-headed (a TRANSFER), then the
    generic run of [w[p:=c].q, x, y, r] (the next phase's datum, with q the new predecessor) reaches after k + 1
    steps the th-image of that list, whose front is c-headed (a REEXEC). -/
theorem replay_reexec (w : T) (q c : Nat) (hw : head w = S) (k : Nat) (a' : T) (rest : List T)
    (hrun : run k (args w ++ [w, var 2, app (var 1) (var 2), var 3]) = some (a' :: rest))
    (hok : runOK w k (args w ++ [w, var 2, app (var 1) (var 2), var 3]))
    (hp : head a' = var 0) :
    run (k + 1) [app (sb c w) (var q), var 1, var 2, var 3] = some ((a' :: rest).map (th w q c)) ∧
      head (th w q c a') = var c := by
  have hna : ¬ wpre w a' := wpre_head w hw 0 a' hp
  refine ⟨?_, th_head0 w q c a' hna hp⟩
  have hw2 : var 2 ≠ w := fun e => by rw [← e] at hw; simp [head] at hw
  have hw3 : var 3 ≠ w := fun e => by rw [← e] at hw; simp [head] at hw
  have hw1 : var 1 ≠ w := fun e => by rw [← e] at hw; simp [head] at hw
  have hwxy : app (var 1) (var 2) ≠ w := fun e => by rw [← e] at hw; simp [head] at hw
  have himg : (args w ++ [w, var 2, app (var 1) (var 2), var 3]).map (th w q c) =
      args (sb c w) ++ [var q, var 2, app (var 1) (var 2), var 3] := by
    rw [sb_args c w hw]
    simp only [List.map_append, List.map_cons, List.map_nil]
    have hargs : (args w).map (th w q c) = (args w).map (sb c) := by
      apply List.map_congr_left
      intro s hs
      exact th_small w q c s (size_args w s hs)
    rw [hargs, th_self w q c]
    simp [th, hw1, hw2, hw3, hwxy]
  have hstep : step [app (sb c w) (var q), var 1, var 2, var 3] =
      some (args (sb c w) ++ [var q, var 2, app (var 1) (var 2), var 3]) := by
    simp [step, head, sb_head c w hw, args]
  have h1 := replay_run w q c k _ _ hok hrun
  rw [himg] at h1
  simp only [run]
  rw [hstep]
  exact h1

#print axioms replay_run
#print axioms replay_reexec
