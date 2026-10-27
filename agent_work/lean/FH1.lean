/-
  agent_work/lean/FH1.lean  (non-universality agent, 2026-10-27).  Lemma FH1, a strengthening of Lemma FH
  (OTD.lean): a level whose wrapper has a FROZEN-HEADED FIRST SPINE ARGUMENT blocks the predecessor.
  Plain Lean 4 core, no Mathlib.  Atoms: var 0 = the live predecessor p; var n with n >= 4 frozen.
  `guarded Lv t`: every occurrence of p in t lies inside an occurrence of Lv.
  Statement (`fh1_main`): let Lv = d.l with args d = u :: _ and u frozen-headed.  If every element of the initial
  list is guarded by Lv, then every reachable list either consists of guarded elements (so its front is not
  p-headed) or has a frozen-headed front (the run is stuck at a re-execution).  In particular no reachable list
  has a p-headed front: the phase can never hand anything to its predecessor.
  Application: if some wrapper v_i of a phase-j handler has a p-headed first spine argument, the next datum
  D_{j+1} = V[y:=p', p:=c] has a level whose wrapper has a c-headed first spine argument: phase j+1 never transfers.
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

def guarded (Lv : T) : T → Prop
  | S => True
  | var n => n ≠ 0
  | app f x => app f x = Lv ∨ (guarded Lv f ∧ guarded Lv x)

/-- some left-spine prefix equals Lv -/
def lpre (Lv : T) : T → Prop
  | S => S = Lv
  | var n => var n = Lv
  | app f x => app f x = Lv ∨ lpre Lv f

theorem guarded_head (Lv : T) (hL : head Lv ≠ var 0) : ∀ t : T, guarded Lv t → head t ≠ var 0
  | S, _ => by simp [head]
  | var n, h => by simp [guarded] at h; simp [head]; exact h
  | app f x, h => by
    rcases h with h | ⟨hf, _⟩
    · rw [h]; exact hL
    · simp [head]; exact guarded_head Lv hL f hf

/-- a guarded S-headed term that is not Lv-prefixed has guarded spine arguments -/
theorem guarded_args (Lv : T) : ∀ t : T, guarded Lv t → head t = S → ¬ lpre Lv t → ∀ s ∈ args t, guarded Lv s
  | S, _, _, _, s, hs => by simp [args] at hs
  | var _, _, hh, _, _, _ => by simp [head] at hh
  | app f x, h, hh, hn, s, hs => by
    have h1 : app f x ≠ Lv := fun e => hn (Or.inl e)
    have h2 : ¬ lpre Lv f := fun e => hn (Or.inr e)
    rcases h with h | ⟨hf, hx⟩
    · exact absurd h h1
    · simp [args] at hs
      rcases hs with hs | hs
      · exact guarded_args Lv f hf (by simpa [head] using hh) h2 s hs
      · subst hs; exact hx

/-- the spine arguments of an Lv-prefixed term start with those of Lv's wrapper -/
theorem args_lpre (d l : T) : ∀ t : T, lpre (app d l) t → ∃ R, args t = args d ++ l :: R
  | S, h => by simp [lpre] at h
  | var _, h => by simp [lpre] at h
  | app f x, h => by
    rcases h with h | h
    · rw [h]; exact ⟨[], by simp [args]⟩
    · obtain ⟨R, hR⟩ := args_lpre d l f h
      exact ⟨R ++ [x], by simp [args, hR]⟩

def FInv (Lv : T) (L : List T) : Prop :=
  (∀ e ∈ L, guarded Lv e) ∨ (∃ u rest, L = u :: rest ∧ ∃ m, 4 ≤ m ∧ head u = var m)

theorem finv_step (d l u : T) (ds : List T) (hd : args d = u :: ds) (m : Nat) (hm : 4 ≤ m)
    (hu : head u = var m) (L L' : List T) (hI : FInv (app d l) L) (hs : step L = some L') :
    FInv (app d l) L' := by
  rcases hI with hG | ⟨u', rest, hL, m', hm', hu'⟩
  · match L, hs, hG with
    | a :: b :: c :: R, hs, hG =>
      simp only [step] at hs
      split at hs
      · rename_i ha
        injection hs with hs; subst hs
        by_cases hpre : lpre (app d l) a
        · right
          obtain ⟨R', hR'⟩ := args_lpre d l a hpre
          refine ⟨u, ds ++ l :: R' ++ c :: app b c :: R, ?_, m, hm, hu⟩
          rw [hR', hd]; simp
        · left
          intro e he; simp at he
          rcases he with he | he | he | he
          · exact guarded_args (app d l) a (hG a (by simp)) ha hpre e he
          · rw [he]; exact hG c (by simp)
          · rw [he]; exact Or.inr ⟨hG b (by simp), hG c (by simp)⟩
          · exact hG e (by simp [he])
      · exact absurd hs (by simp)
  · subst hL
    match rest, hs with
    | b :: c :: R, hs =>
      simp only [step] at hs
      rw [hu'] at hs
      simp at hs

theorem finv_run (d l u : T) (ds : List T) (hd : args d = u :: ds) (m : Nat) (hm : 4 ≤ m)
    (hu : head u = var m) : ∀ (k : Nat) (L L' : List T), FInv (app d l) L → run k L = some L' →
    FInv (app d l) L'
  | 0, L, L', hI, h => by simp [run] at h; subst h; exact hI
  | k + 1, L, L', hI, h => by
    simp only [run] at h
    split at h
    · rename_i L1 hs
      exact finv_run d l u ds hd m hm hu k L1 L' (finv_step d l u ds hd m hm hu L L1 hI hs) h
    · exact absurd h (by simp)

/-- **Lemma FH1.**  If every element of the initial list is guarded by the level Lv = d.l whose wrapper d has a
    frozen-headed first spine argument, no reachable list has a p-headed front. -/
theorem fh1_main (d l u : T) (ds : List T) (hd : args d = u :: ds) (m : Nat) (hm : 4 ≤ m)
    (hu : head u = var m) (hdS : head d = S) (k : Nat) (L0 : List T) (a : T) (rest : List T)
    (h0 : ∀ e ∈ L0, guarded (app d l) e) (hrun : run k L0 = some (a :: rest)) : head a ≠ var 0 := by
  rcases finv_run d l u ds hd m hm hu k L0 _ (Or.inl h0) hrun with hG | ⟨u', r', hL, m', hm', hu'⟩
  · have hLv : head (app d l) ≠ var 0 := by simp [head, hdS]
    exact guarded_head (app d l) hLv a (hG a (by simp))
  · injection hL with h1 _
    subst h1
    rw [hu']; intro h; injection h with h; omega

#print axioms fh1_main
