"""Generate lean/LP1.lean: Lemma P (descent lemma, contrapositive form) and Theorem LP1 (outside the five D2 classes of
M35, the leftmost Böhm-tree path ends at the leaf S), on top of lean/Q10.lean (main agent, 2026-10-27).
Usage: python gen_lp1.py [dev]"""
import sys, re
from verify_model import load
from symb import parse

reps, F, T = load("../data/model35_hn.txt")


def lean_term(t):
    if t == "S":
        return "S"
    f, x = t
    return f"(app {lean_term(f)} {lean_term(x)})"


D2 = [a for a in range(35) if F[a] and all(not F[int(T[int(T[a, b]), c])] for b in range(35) for c in range(35))]
assert D2 == [24, 26, 28, 31, 34], D2
rep_list = ", ".join(lean_term(parse(r)) for r in reps)

part = '''
/-! ## Lemma P (descent lemma) and Theorem LP1 -/

/-- the leftmost Böhm-tree path from the node S·L ends at the leaf S -/
inductive LeftEnd : List Tm → Prop
  | leaf (L : List Tm) (n : Nat) : run n L = some [] → LeftEnd L
  | node (L : List Tm) (n : Nat) (x : Tm) (rest : List Tm) : run n L = some (x :: rest) →
      (x :: rest).length ≤ 2 → LeftEnd (args x) → LeftEnd L

/-- a run with material appended reaches an hnf only after the prefix reached its own hnf -/
theorem run_prefix_hnf : ∀ (N : Nat) (P R H : List Tm), R ≠ [] → run N (P ++ R) = some H → H.length ≤ 2 →
    ∃ n P', n ≤ N ∧ run n P = some P' ∧ P'.length ≤ 2 := by
  intro N
  induction N with
  | zero =>
    intro P R H hR h hH
    simp [run] at h
    subst h
    refine ⟨0, P, Nat.le_refl 0, rfl, ?_⟩
    have := hH; simp at this
    have : R.length ≥ 1 := by cases R with | nil => exact absurd rfl hR | cons _ _ => simp
    omega
  | succ N ih =>
    intro P R H hR h hH
    rcases Nat.lt_or_ge 2 P.length with hP | hP
    · match P, hP with
      | a :: b :: c :: T0, _ =>
        have hs : step (a :: b :: c :: T0) = some (args a ++ c :: app b c :: T0) := rfl
        have hs2 := step_append _ _ R hs
        rw [run_succ N _ _ hs2] at h
        obtain ⟨n, P', hn, hr, hl⟩ := ih _ R H hR h hH
        exact ⟨n + 1, P', by omega, by rw [run_succ n _ _ hs]; exact hr, hl⟩
    · exact ⟨0, P, Nat.zero_le _, rfl, hP⟩

/-- **Lemma P** (contrapositive form): if S·L·A·B has a head normal form, the leftmost path of S·L ends at S -/
theorem lemmaP : ∀ (N : Nat) (L : List Tm) (A B : Tm) (H : List Tm),
    run N (L ++ [A, B]) = some H → H.length ≤ 2 → LeftEnd L := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro L A B H h hH
    obtain ⟨n0, L', hn0, h0, hl0⟩ := run_prefix_hnf N L [A, B] H (by simp) h hH
    have ha := run_append n0 L L' [A, B] h0
    have hrest : run (N - n0) (L' ++ [A, B]) = some H := by
      have := run_add n0 (N - n0) _ _ ha
      rw [show n0 + (N - n0) = N by omega, h] at this
      exact this.symm
    match L', hl0, h0, hrest with
    | [], _, h0, _ => exact LeftEnd.leaf L n0 h0
    | [x], _, h0, hrest =>
      have hpos : N - n0 ≠ 0 := by
        intro hz; rw [hz] at hrest; simp [run] at hrest; subst hrest; simp at hH
      obtain ⟨m, hm⟩ : ∃ m, N - n0 = m + 1 := ⟨N - n0 - 1, by omega⟩
      rw [hm] at hrest
      have hs : step ([x] ++ [A, B]) = some (args x ++ [B, app A B]) := by simp [step]
      rw [run_succ m _ _ hs] at hrest
      exact LeftEnd.node L n0 x [] h0 (by simp) (ih m (by omega) (args x) B (app A B) H hrest hH)
    | [x, y], _, h0, hrest =>
      have hpos : N - n0 ≠ 0 := by
        intro hz; rw [hz] at hrest; simp [run] at hrest; subst hrest; simp at hH
      obtain ⟨m, hm⟩ : ∃ m, N - n0 = m + 1 := ⟨N - n0 - 1, by omega⟩
      rw [hm] at hrest
      have hs : step ([x, y] ++ [A, B]) = some ((args x ++ [A, app y A]) ++ [B]) := by simp [step]
      rw [run_succ m _ _ hs] at hrest
      obtain ⟨k, H', hk, hr', hl'⟩ := run_prefix_hnf m (args x ++ [A, app y A]) [B] H (by simp) hrest hH
      exact LeftEnd.node L n0 x [y] h0 (by simp) (ih k (by omega) (args x) A (app y A) H' hr' hl')
    | _ :: _ :: _ :: _, hl0, _, _ => simp at hl0

/-- representatives of the 35 M35 classes (data/model35_hn.txt) -/
def repL : List Tm := [''' + rep_list + ''']
def checkReps : Bool := (List.range 35).all fun k => cls (repL.getD k S) == k
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem kreps : checkReps = true := by decide +kernel

/-- D2 = {24, 26, 28, 31, 34}: every F class outside D2 has two arguments giving an F class -/
def checkD2 : Bool := (List.range 35).all fun a =>
  !isF a || [24, 26, 28, 31, 34].contains a ||
  (List.range 35).any fun b => (List.range 35).any fun c => isF (mul (mul a b) c)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem kd2 : checkD2 = true := by decide +kernel

/-- **Theorem LP1.** If the M35 class of t is in F but not in D2, the leftmost Böhm-tree path of t ends at the leaf S. -/
theorem LP1 (t : Tm) (hF : isF (cls t) = true) (hD : cls t ∉ [24, 26, 28, 31, 34]) : LeftEnd (args t) := by
  have hk := kd2
  simp only [checkD2, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.contains_iff_mem] at hk
  rcases hk (cls t) (cls_lt t) with (h1 | h1) | ⟨b, hb, c, hc, hbc⟩
  · rw [hF] at h1; exact absurd h1 (by decide)
  · exact absurd h1 hD
  · have hr := kreps
    simp only [checkReps, List.all_eq_true, List.mem_range, beq_iff_eq] at hr
    have hA := hr b hb
    have hB := hr c hc
    have hcls : cls (app (app t (repL.getD b S)) (repL.getD c S)) = mul (mul (cls t) b) c := by
      simp only [cls]; rw [hA, hB]
    obtain ⟨n, L', h, hl⟩ := (Q10 (app (app t (repL.getD b S)) (repL.getD c S))).2 (by rw [hcls]; exact hbc)
    have hargs : args (app (app t (repL.getD b S)) (repL.getD c S)) = args t ++ [repL.getD b S, repL.getD c S] := by
      simp [args]
    rw [hargs] at h
    exact lemmaP n (args t) _ _ L' h hl

#print axioms lemmaP
#print axioms LP1
'''
base = open("../lean/Q10.lean", encoding="utf-8").read().replace("#print axioms k1\n#print axioms k7\n#print axioms Q10\n", "")
base = base.replace("Theorem Q10 in Lean (main agent, 2026-10-27)",
                    "Lemma P and Theorem LP1 in Lean (main agent, 2026-10-27), on top of Theorem Q10")
out = base + part
target = "../lean/LP1.lean"
if len(sys.argv) > 1 and sys.argv[1] == "dev":
    for k in ["k1", "k2", "k3", "k4", "k5", "k6", "k7"]:
        out = re.sub(r"(theorem %s : check\w+ = true := by) decide \+kernel" % k, r"\1 sorry", out)
    target = "../lean/LP1dev.lean"
open(target, "w", encoding="utf-8").write(out)
print(target, "written,", out.count("\n"), "lines")
