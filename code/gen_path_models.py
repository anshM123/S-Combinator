"""Generate lean/PathModels.lean: Proposition Q'' (the 'infinite' halves of the leftmost-path model L36 and the
rightmost-path model R19), on top of lean/Q10.lean (main agent, 2026-10-27). Tables come mechanically from the data
files. Usage: python gen_path_models.py [dev]   (dev: stub the kernel checks with sorry for fast iteration)"""
import sys, re
from verify_model import load

Mr, MF, MT = load("../data/model35_hn.txt")
mM = lambda a, b: int(MT[a, b])


def section(T, path, side):
    Lr, LF, LT = load(path)
    n = len(Lr)
    assert Lr[0] == "S"
    mL = lambda a, b: int(LT[a, b])
    big = 0
    for a in reversed(range(n)):
        for b in reversed(range(n)):
            big = big * n + mL(a, b)
    fmask = sum(1 << k for k in range(n) if LF[k])
    J = {(0, 0)}
    fr = [(0, 0)]
    while fr:
        new = []
        for a in list(J):
            for b in list(J):
                for x, y in ((a, b), (b, a)):
                    c = (mL(x[0], y[0]), mM(x[1], y[1]))
                    if c not in J:
                        J.add(c)
                        new.append(c)
        fr = new
    J = sorted(J)
    pick = "x" if side == "left" else "y"
    if side == "left":
        cont_def = f"∃ x rest, L' = x :: rest ∧ Inf{T} d (args x)"
        one = f"exact ⟨x, [], rfl, inf{T}_aux d (args x) hx⟩"
        two_have = f"have hx : flag{T} (clsL{T} (args x)) = true := by rw [← cls{T}_args]; exact hz.symm"
        two = f"exact ⟨x, [y], rfl, inf{T}_aux d (args x) hx⟩"
    else:
        cont_def = f"∃ x, L'.getLast? = some x ∧ Inf{T} d (args x)"
        one = f"exact ⟨x, rfl, inf{T}_aux d (args x) hx⟩"
        two_have = f"have hy : flag{T} (clsL{T} (args y)) = true := by rw [← cls{T}_args]; exact hz.symm"
        two = f"exact ⟨y, rfl, inf{T}_aux d (args y) hy⟩"
    jl = ", ".join(f"({p}, {m})" for p, m in J)
    return f'''
/-! ## {T}: the {side}most-path model ({n} classes): flag 1 => the {side}most Böhm-tree path is infinite -/

def TAB{T} : Nat := {big}
def mul{T} (a b : Nat) : Nat := (TAB{T} / {n} ^ ({n} * a + b)) % {n}
def FMASK{T} : Nat := {fmask}
def flag{T} (k : Nat) : Bool := (FMASK{T} / 2 ^ k) % 2 == 1
def J{T} : List (Nat × Nat) := [{jl}]
def cls{T} : Tm → Nat
  | S => 0
  | app f x => mul{T} (cls{T} f) (cls{T} x)
def clsL{T} (L : List Tm) : Nat := L.foldl (fun acc t => mul{T} acc (cls{T} t)) 0
def RN{T} : List Nat := List.range {n}
def checkS{T} : Bool := RN{T}.all fun x => RN{T}.all fun y => RN{T}.all fun z =>
  mul{T} (mul{T} (mul{T} 0 x) y) z == mul{T} (mul{T} x z) (mul{T} y z)
def checkR{T} : Bool := RN{T}.all fun x => RN{T}.all fun y => mul{T} x y < {n}
def checkC{T} : Bool := !flag{T} 0 && (RN{T}.all fun x => flag{T} (mul{T} 0 x) == flag{T} x) &&
  (RN{T}.all fun x => RN{T}.all fun y => flag{T} (mul{T} (mul{T} 0 x) y) == flag{T} {pick})
def checkJ{T} : Bool := J{T}.contains (0, 0) &&
  (J{T}.all fun a => J{T}.all fun b => J{T}.contains (mul{T} a.1 b.1, mul a.2 b.2)) &&
  (J{T}.all fun a => !flag{T} a.1 || isF a.2)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem kS{T} : checkS{T} = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem kR{T} : checkR{T} = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem kC{T} : checkC{T} = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem kJ{T} : checkJ{T} = true := by decide +kernel

theorem cls{T}_lt : ∀ t : Tm, cls{T} t < {n}
  | S => by simp [cls{T}]
  | app f x => by
    have h := kR{T}
    simp only [checkR{T}, RN{T}, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h _ (cls{T}_lt f) _ (cls{T}_lt x)

theorem cls{T}_args : ∀ t : Tm, cls{T} t = clsL{T} (args t)
  | S => by simp [cls{T}, clsL{T}, args]
  | app f x => by
    simp only [cls{T}, clsL{T}, args, List.foldl_append, List.foldl]
    rw [cls{T}_args f]; rfl

theorem clsL{T}_step (L L' : List Tm) (h : step L = some L') : clsL{T} L = clsL{T} L' := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step, Option.some.injEq] at h
    subst h
    simp only [clsL{T}, List.foldl_append, List.foldl]
    have e : (args a).foldl (fun acc t => mul{T} acc (cls{T} t)) 0 = cls{T} a := (cls{T}_args a).symm
    have hk := kS{T}
    simp only [checkS{T}, RN{T}, List.all_eq_true, List.mem_range, beq_iff_eq] at hk
    rw [e, hk _ (cls{T}_lt a) _ (cls{T}_lt b) _ (cls{T}_lt c)]
    rfl

theorem clsL{T}_run : ∀ (n : Nat) (L L' : List Tm), run n L = some L' → clsL{T} L = clsL{T} L'
  | 0, L, L', h => by simp [run] at h; subst h; rfl
  | n + 1, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 => rw [hs] at h; exact (clsL{T}_step L L1 hs).trans (clsL{T}_run n L1 L' h)

theorem joint{T}_term : ∀ t : Tm, (cls{T} t, cls t) ∈ J{T}
  | S => by
    have h := kJ{T}
    simp only [checkJ{T}, Bool.and_eq_true, List.contains_iff_mem] at h
    exact h.1.1
  | app f x => by
    have h := kJ{T}
    simp only [checkJ{T}, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
    exact h.1.2 _ (joint{T}_term f) _ (joint{T}_term x)

theorem joint{T}_list : ∀ (L : List Tm) (acc : Nat × Nat), acc ∈ J{T} →
    (L.foldl (fun a t => mul{T} a (cls{T} t)) acc.1, L.foldl (fun a t => mul a (cls t)) acc.2) ∈ J{T}
  | [], acc, h => by simpa using h
  | t :: L, acc, h => by
    simp only [List.foldl]
    have hk := kJ{T}
    simp only [checkJ{T}, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hk
    exact joint{T}_list L (mul{T} acc.1 (cls{T} t), mul acc.2 (cls t)) (hk.1.2 _ h _ (joint{T}_term t))

theorem flag{T}_F (L : List Tm) (h : flag{T} (clsL{T} L) = true) : isF (clsL L) = true := by
  have hk := kJ{T}
  simp only [checkJ{T}, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Bool.or_eq_true,
    Bool.not_eq_true'] at hk
  have hm := joint{T}_list L (0, 0) hk.1.1
  rcases hk.2 _ hm with h1 | h1
  · exact absurd h (by simp only [clsL{T}] at h1 ⊢; rw [h1]; decide)
  · exact h1

/-- the {side}most Böhm-tree path has at least d further nodes, each with a head normal form -/
def Inf{T} : Nat → List Tm → Prop
  | 0, _ => True
  | d + 1, L => ∃ n L', run n L = some L' ∧ L'.length ≤ 2 ∧ {cont_def}

theorem inf{T}_aux : ∀ (d : Nat) (L : List Tm), flag{T} (clsL{T} L) = true → Inf{T} d L
  | 0, _, _ => trivial
  | d + 1, L, h => by
    obtain ⟨n, L', hr, hl⟩ := hnfF L (flag{T}_F L h)
    have hc : clsL{T} L' = clsL{T} L := (clsL{T}_run n L L' hr).symm
    rw [← hc] at h
    have hk := kC{T}
    simp only [checkC{T}, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, RN{T},
      Bool.not_eq_true'] at hk
    obtain ⟨⟨h0, h1⟩, h2⟩ := hk
    refine ⟨n, L', hr, hl, ?_⟩
    match L', hl with
    | [], _ => simp only [clsL{T}, List.foldl] at h; rw [h0] at h; exact absurd h (by decide)
    | [x], _ =>
      simp only [clsL{T}, List.foldl] at h
      have hx : flag{T} (clsL{T} (args x)) = true := by rw [← cls{T}_args, ← h1 _ (cls{T}_lt x)]; exact h
      {one}
    | [x, y], _ =>
      simp only [clsL{T}, List.foldl] at h
      have hz := h2 _ (cls{T}_lt x) _ (cls{T}_lt y)
      rw [h] at hz
      {two_have}
      {two}

/-- Proposition Q'' ({side}most path): if the {T} class of t is flagged, the {side}most path of BT(t) is infinite. -/
theorem propQ2{T} (t : Tm) (h : flag{T} (cls{T} t) = true) : ∀ d, Inf{T} d (args t) :=
  fun d => inf{T}_aux d (args t) (by rw [← cls{T}_args]; exact h)
'''


base = open("../lean/Q10.lean", encoding="utf-8").read().replace("#print axioms k1\n#print axioms k7\n#print axioms Q10\n", "")
base = base.replace("Theorem Q10 in Lean (main agent, 2026-10-27)",
                    "Proposition Q'' (path models L36, R19) in Lean (main agent, 2026-10-27), on top of Theorem Q10")
out = base + section("Lft", "../data/model36_leftpath.txt", "left") + section("Rgt", "../data/model19_rightpath.txt", "right")
out += "\n#print axioms propQ2Lft\n#print axioms propQ2Rgt\n#print axioms kSLft\n"
target = "../lean/PathModels.lean"
if len(sys.argv) > 1 and sys.argv[1] == "dev":
    for k in ["k1", "k2", "k3", "k4", "k5", "k6", "k7", "kSLft", "kRLft", "kCLft", "kJLft", "kSRgt", "kRRgt", "kCRgt", "kJRgt"]:
        out = re.sub(r"(theorem %s : check\w+ = true := by) decide \+kernel" % k, r"\1 sorry", out)
    target = "../lean/PathModelsdev.lean"
open(target, "w", encoding="utf-8").write(out)
print(target, "written,", out.count("\n"), "lines")
