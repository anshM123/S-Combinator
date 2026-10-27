"""Generate lean/URObs.lean = lean/URCore.lean + the Observation: `urForever L` holds iff at every step of the run the
term S·L has exactly one redex (main agent, 2026-10-27). Usage: python gen_urobs.py"""
import re

part = '''
/-! ## The Observation: urForever means "exactly one redex at every step" -/

namespace Tm

/-- a redex S x y z -/
def isRedex : Tm → Bool
  | app (app (app S _) _) _ => true
  | _ => false

/-- number of redex occurrences -/
def nred : Tm → Nat
  | S => 0
  | app f a => nred f + nred a + (if isRedex (app f a) then 1 else 0)

/-- a normal form has no redex, and conversely -/
theorem nf_iff_nred : ∀ t : Tm, nf t ↔ nred t = 0
  | S => by simp [nf, nred]
  | app f a => by
    have ihf := nf_iff_nred f
    have iha := nf_iff_nred a
    constructor
    · intro h
      obtain ⟨hl, hf, ha⟩ := h
      have e1 := ihf.1 hf
      have e2 := iha.1 ha
      have e3 : isRedex (app f a) = false := by
        match f, hl with
        | S, _ => rfl
        | app S _, _ => rfl
        | app (app S _) _, hl => simp [args] at hl
        | app (app (app _ _) _) _, _ => rfl
      simp [nred, e1, e2, e3]
    · intro h
      simp only [nred, Nat.add_eq_zero_iff] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨?_, ihf.2 h1, iha.2 h2⟩
      -- no redex at the root and none in f: f has at most one argument
      match f, h1, h3 with
      | S, _, _ => simp [args]
      | app S _, _, _ => simp [args]
      | app (app S _) _, _, h3 => simp [isRedex] at h3
      | app (app (app g x) y) z, h1, _ =>
        -- f = (g x y) z has a node with three arguments (a redex) somewhere on its spine
        exfalso
        have key : ∀ t : Tm, 3 ≤ (args t).length → 1 ≤ nred t := by
          intro t ht
          induction t with
          | S => simp [args] at ht
          | app p q ihp _ =>
            simp only [nred]
            by_cases hp : 3 ≤ (args p).length
            · have := ihp hp; omega
            · have hp2 : (args p).length = 2 := by simp [args] at ht; omega
              match p, hp2 with
              | app (app S _) _, _ => simp [isRedex]
              | S, h => simp [args] at h
              | app S _, h => simp [args] at h
              | app (app (app _ _) _) _, h => simp [args] at h
        have hlen : 3 ≤ (args (app (app (app g x) y) z)).length := by simp [args]
        have := key _ hlen
        omega

end Tm

open Tm

/-- the term S·L -/
def spineTerm (L : List Tm) : Tm := L.foldl app S

theorem args_foldl : ∀ (L : List Tm) (t : Tm), args (L.foldl app t) = args t ++ L
  | [], t => by simp
  | e :: L, t => by simp only [List.foldl]; rw [args_foldl L (app t e)]; simp [args]

def nsum : List Tm → Nat
  | [] => 0
  | e :: L => nred e + nsum L

/-- redexes of S·L: those inside the elements, plus the head redex when L has at least three elements -/
theorem nred_foldl : ∀ (L : List Tm) (t : Tm),
    nred (L.foldl app t) = nred t + nsum L + (if (args t).length < 3 ∧ 3 ≤ (args t).length + L.length then 1 else 0)
  | [], t => by simp [nsum]
  | e :: L, t => by
    simp only [List.foldl]
    rw [nred_foldl L (app t e)]
    simp only [nred, nsum, args, List.length_append, List.length_cons, List.length_nil]
    have hr : isRedex (app t e) = true ↔ (args t).length = 2 := by
      match t with
      | S => simp [isRedex, args]
      | app S _ => simp [isRedex, args]
      | app (app S _) _ => simp [isRedex, args]
      | app (app (app _ _) _) _ => simp [isRedex, args]
    by_cases h2 : (args t).length = 2
    · have := hr.2 h2
      simp only [this, ite_true]
      split <;> split <;> omega
    · have : isRedex (app t e) = false := by
        cases h : isRedex (app t e)
        · rfl
        · exact absurd (hr.1 h) h2
      simp only [this, Bool.false_eq_true, ite_false]
      split <;> split <;> omega

theorem nred_spine (L : List Tm) (h : 3 ≤ L.length) : nred (spineTerm L) = 1 + nsum L := by
  unfold spineTerm
  rw [nred_foldl]
  simp [nred, args]
  split <;> omega

theorem nsum_zero : ∀ L : List Tm, nsum L = 0 ↔ ∀ e ∈ L, nf e
  | [] => by simp [nsum]
  | e :: L => by
    simp only [nsum, Nat.add_eq_zero_iff, List.mem_cons, forall_eq_or_imp]
    rw [nsum_zero L, nf_iff_nred e]

/-- one redex at a list of length >= 3 means all elements are normal forms -/
theorem one_redex_iff (L : List Tm) (h : 3 ≤ L.length) : nred (spineTerm L) = 1 ↔ ∀ e ∈ L, nf e := by
  rw [nred_spine L h, ← nsum_zero]
  omega

/-- **The Observation.** The run from L keeps a unique redex for ever (`urForever`) iff at every step n the run has a
    list L' with at least three elements and the term S·L' has exactly one redex (the head redex). Since a term with one
    redex has only one possible step, every evaluation order (and the multiway system) follows this run. -/
theorem observation (L : List Tm) :
    urForever L ↔ ∀ n, ∃ L', run n L = some L' ∧ 3 ≤ L'.length ∧ nred (spineTerm L') = 1 := by
  constructor
  · intro hu n
    obtain ⟨L', h1, hg⟩ := hu n
    match L', hg with
    | a :: b :: c :: R, hg =>
      refine ⟨_, h1, by simp, ?_⟩
      rw [one_redex_iff _ (by simp)]
      exact hg.1
  · intro h n
    obtain ⟨L', h1, hl, hr⟩ := h n
    obtain ⟨L'', h2, hl2, hr2⟩ := h (n + 1)
    have hall := (one_redex_iff L' hl).1 hr
    match L', hl, h1, hall with
    | a :: b :: c :: R, _, h1, hall =>
      refine ⟨_, h1, hall, ?_⟩
      -- the next list contains b·c, a normal form, so b has at most one argument
      have hs : step (a :: b :: c :: R) = some (args a ++ c :: app b c :: R) := rfl
      have e : run (n + 1) L = some (args a ++ c :: app b c :: R) := by
        have := run_add n 1 L _ h1
        rw [this]; simp [run, hs]
      rw [e] at h2
      simp only [Option.some.injEq] at h2
      subst h2
      have hall2 := (one_redex_iff _ hl2).1 hr2
      have hbc := hall2 (app b c) (by simp)
      exact by simp [nf] at hbc; omega

#print axioms observation
'''


def main():
    base = open("../lean/URCore.lean", encoding="utf-8").read()
    base = re.sub(r"#print axioms \w+\n", "", base)
    has_run_add = "theorem run_add" in base
    extra = ""
    if not has_run_add:
        extra = '''
theorem run_add : ∀ (m n : Nat) (L L' : List Tm), run m L = some L' → run (m + n) L = run n L'
  | 0, n, L, L', h => by simp [run] at h; subst h; simp
  | m + 1, n, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 =>
      rw [hs] at h
      rw [show m + 1 + n = (m + n) + 1 by omega]
      simp only [run, hs]; exact run_add m n L1 L' h
'''
    out = base + extra + part
    open("../lean/URObs.lean", "w", encoding="utf-8").write(out)
    print("lean/URObs.lean written,", out.count("\n"), "lines; run_add present in base:", has_run_add)


main()
