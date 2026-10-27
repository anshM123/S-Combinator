inductive Tm where
  | S : Tm
  | app : Tm → Tm → Tm
deriving DecidableEq, Repr

def Tm.size : Tm → Nat
  | .S => 1
  | .app f x => f.size + x.size

theorem size_pos (t : Tm) : 0 < t.size := by
  cases t <;> simp [Tm.size] <;> omega

example : (Tm.app .S .S).size = 2 := by decide
