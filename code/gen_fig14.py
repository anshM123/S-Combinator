"""Generate lean/BEKW_Q10.lean = lean/Q10.lean + BEKW Question 10 in its original form: the tree automaton of BEKW
Figure 14 (transcribed in data/bekw_fig14_table.json, state 34 = the paper's ∞) accepts exactly the closed S-terms
with a head normal form. The isomorphism M35 -> Fig. 14 (E8) is checked by the Lean kernel (main agent, 2026-10-27).
Usage: python gen_fig14.py"""
import json
from verify_model import load

reps, F, T = load("../data/model35_hn.txt")
fig = json.load(open("../data/bekw_fig14_table.json"))
n = 35
assert len(fig) == n and all(len(r) == n for r in fig)
INF = 34
# the generator-preserving isomorphism found in E8 (33 is M35's bottom class, mapped to the paper's ∞ = 34)
phi = {0: 0, 1: 1, 2: 2, 3: 6, 4: 3, 5: 7, 6: 11, 7: 14, 8: 4, 9: 8, 10: 12, 11: 15, 12: 13, 13: 16, 14: 18, 15: 26,
       16: 5, 17: 9, 18: 19, 19: 27, 20: 17, 21: 20, 22: 22, 23: 28, 24: 24, 25: 31, 26: 10, 27: 21, 28: 23, 29: 29,
       30: 30, 31: 25, 32: 32, 33: INF, 34: 33}
# sanity in Python before generating
for a in range(n):
    for b in range(n):
        assert phi[int(T[a, b])] == fig[phi[a]][phi[b]], (a, b)
assert sorted(phi.values()) == list(range(n))
assert all((F[a] == 1) == (phi[a] != INF) for a in range(n))

big = 0
for a in reversed(range(n)):
    for b in reversed(range(n)):
        big = big * n + fig[a][b]
phil = ", ".join(str(phi[k]) for k in range(n))

part = f'''
/-! ## BEKW Question 10 in its original form: the automaton of BEKW Figure 14 -/

/-- the transition table of BEKW Figure 14 (data/bekw_fig14_table.json; state 34 is the paper's ∞, state 0 is S) -/
def FIGTAB : Nat := {big}
def figmul (a b : Nat) : Nat := (FIGTAB / 35 ^ (35 * a + b)) % 35

/-- the state of a term in the Figure 14 automaton -/
def figcls : Tm → Nat
  | S => 0
  | app f x => figmul (figcls f) (figcls x)

/-- the isomorphism M35 -> Figure 14 (E8) -/
def PHI : List Nat := [{phil}]
def phi (k : Nat) : Nat := PHI.getD k 0

/-- kernel check: phi is a homomorphism on all 1,225 products, preserves the generator, and maps F onto the
    non-∞ states; it is a bijection (all 35 values distinct and < 35) -/
def checkIso : Bool :=
  phi 0 == 0 &&
  ((List.range 35).all fun a => (List.range 35).all fun b => phi (mul a b) == figmul (phi a) (phi b)) &&
  ((List.range 35).all fun a => isF a == (phi a != 34)) &&
  ((List.range 35).all fun a => decide (phi a < 35)) &&
  ((List.range 35).all fun a => (List.range 35).all fun b => a == b || phi a != phi b)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem kiso : checkIso = true := by decide +kernel

theorem figcls_phi : ∀ t : Tm, figcls t = phi (cls t)
  | S => by
    have h := kiso
    simp only [checkIso, Bool.and_eq_true, beq_iff_eq] at h
    simp only [figcls, cls]
    exact h.1.1.1.1.symm
  | app f x => by
    have h := kiso
    simp only [checkIso, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    simp only [figcls, cls, figcls_phi f, figcls_phi x]
    exact (h.1.1.1.2 _ (cls_lt f) _ (cls_lt x)).symm

/-- **BEKW Question 10, as posed.** The tree automaton of BEKW Figure 14 accepts (does not reach the state ∞) exactly
    the closed S-terms that have a head normal form. -/
theorem bekw_q10 (t : Tm) : (∃ n L', run n (args t) = some L' ∧ L'.length ≤ 2) ↔ figcls t ≠ 34 := by
  rw [Q10 t, figcls_phi t]
  have h := kiso
  simp only [checkIso, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have e := h.1.1.2 (cls t) (cls_lt t)
  rw [e]
  simp

#print axioms kiso
#print axioms bekw_q10
'''
base = open("../lean/Q10.lean", encoding="utf-8").read().replace("#print axioms k1\n#print axioms k7\n#print axioms Q10\n", "")
base = base.replace("Theorem Q10 in Lean (main agent, 2026-10-27)",
                    "BEKW Question 10 in its original form (the automaton of BEKW Figure 14) in Lean (main agent, 2026-10-27), on top of Theorem Q10")
out = base + part
open("../lean/BEKW_Q10.lean", "w", encoding="utf-8").write(out)
print("lean/BEKW_Q10.lean written,", out.count("\n"), "lines")
