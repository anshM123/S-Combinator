"""Generate lean/Lemma4.lean = lean/Q10.lean + Lemma 4 (all terms without a head normal form are one syntactic class:
interchangeable in every context) and the congruence of head normalisation, as corollaries of Theorem Q10 (main
agent, 2026-10-27). Usage: python gen_lemma4.py"""
part = '''
/-! ## Lemma 4: all head-unstable terms are one syntactic class -/

def HasHnf (t : Tm) : Prop := ∃ n L', run n (args t) = some L' ∧ L'.length ≤ 2

/-- one-hole contexts -/
inductive Ctx where
  | hole : Ctx
  | appL : Ctx → Tm → Ctx
  | appR : Tm → Ctx → Ctx

def plug : Ctx → Tm → Tm
  | Ctx.hole, u => u
  | Ctx.appL C x, u => app (plug C u) x
  | Ctx.appR f C, u => app f (plug C u)

theorem cls_plug (t t' : Tm) (h : cls t = cls t') : ∀ C : Ctx, cls (plug C t) = cls (plug C t')
  | Ctx.hole => h
  | Ctx.appL C x => by simp only [plug, cls, cls_plug t t' h C]
  | Ctx.appR f C => by simp only [plug, cls, cls_plug t t' h C]

/-- M35 has exactly one class outside F (class 33, the class of S(SSS)S(SSS)) -/
def checkBot : Bool := (List.range 35).all fun k => isF k || k == 33
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem kbot : checkBot = true := by decide +kernel

theorem bot_unique (t : Tm) (h : ¬ HasHnf t) : cls t = 33 := by
  have hF : isF (cls t) = false := by
    cases hc : isF (cls t)
    · rfl
    · exact absurd ((Q10 t).2 hc) h
  have hk := kbot
  simp only [checkBot, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hk
  rcases hk (cls t) (cls_lt t) with h1 | h1
  · rw [hF] at h1; exact absurd h1 (by decide)
  · exact h1

/-- **Congruence.** Terms with the same M35 class have a head normal form in exactly the same contexts. -/
theorem hnf_congr (t t' : Tm) (h : cls t = cls t') (C : Ctx) : HasHnf (plug C t) ↔ HasHnf (plug C t') := by
  unfold HasHnf
  rw [Q10, Q10, cls_plug t t' h C]

/-- **Lemma 4.** If t and t' both have no head normal form, then for every one-hole context C, C[t] has a head normal
    form iff C[t'] has one. -/
theorem lemma4 (t t' : Tm) (ht : ¬ HasHnf t) (ht' : ¬ HasHnf t') (C : Ctx) : HasHnf (plug C t) ↔ HasHnf (plug C t') :=
  hnf_congr t t' ((bot_unique t ht).trans (bot_unique t' ht').symm) C

#print axioms lemma4
#print axioms hnf_congr
'''
base = open("../lean/Q10.lean", encoding="utf-8").read().replace("#print axioms k1\n#print axioms k7\n#print axioms Q10\n", "")
base = base.replace("Theorem Q10 in Lean (main agent, 2026-10-27)",
                    "Lemma 4 (head-unstable terms are one syntactic class) in Lean (main agent, 2026-10-27), on top of Theorem Q10")
out = base + part
open("../lean/Lemma4.lean", "w", encoding="utf-8").write(out)
print("lean/Lemma4.lean written,", out.count("\n"), "lines")
