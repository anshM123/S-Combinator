
/-! ### Counterexample to Conjecture R3 as stated for ALL ordered data (two occurrences of p).
    D = S(Sp)(S(S(S(SS)(SS)p))) (p = var 0, x = var 1, y = var 2, r = var 3, c = var 4 frozen).
    Phase 2 transfers w.y with w = S(S(S(SS)(SS)p)) after 2 steps; the next datum w[p:=c].p' (p' = var 0 again)
    reaches after 7 steps a p'-front with the proper y-comb (c.(SSc)).(p'.y) at position 3. -/

def cxS : T := S
def cxP : T := var 0
def cxW : T := app S (app S (app (app (app S (app S S)) (app S S)) cxP))
def cxD : T := app (app S (app S cxP)) cxW

theorem r3_cx_phase2 :
    run 2 [cxD, var 1, var 2, var 3] =
      some [var 0, var 2, app cxW (var 2), app (var 1) (var 2), var 3] := by
  rfl

/-- the next datum: w[p := c].p' with c = var 4 -/
def cxW' : T := app S (app S (app (app (app S (app S S)) (app S S)) (var 4)))
def cxD3 : T := app cxW' (var 0)

theorem r3_cx_next : asub (sg3 4) (app cxW (var 2)) = cxD3 := by rfl

theorem r3_cx_phase3 :
    run 7 [cxD3, var 1, var 2, var 3] =
      some [app (var 0) (var 2), app (var 4) (app (var 0) (var 2)),
            app (app (var 4) (app (app S S) (var 4))) (app (var 0) (var 2)),
            app (var 2) (app (var 0) (var 2)), app (var 1) (var 2), var 3] := by
  rfl

/-- copies of INNER.lean's `closed` / `ordered` (renamed): cxD satisfies the hypotheses of ordered_innermost -/
def iclosed : T → Prop
  | S => True
  | var n => 4 ≤ n
  | app f x => iclosed f ∧ iclosed x

def iordered : T → Prop
  | app f x => (head f = S → (iclosed x → iclosed f)) ∧ iordered f ∧ iordered x
  | _ => True

theorem r3_cx_ordered : iordered cxD ∧ head cxD = S ∧ occ2 cxD = 0 := by
  simp [iordered, iclosed, cxD, cxW, cxP, head, occ2]
