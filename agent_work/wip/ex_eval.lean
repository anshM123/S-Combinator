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
-- D = S(S(S(S(SS))S))(S(SS)p)
def SS : T := app S S
def D : T := app (app S (app S (app (app S (app S SS)) S))) (app (app S SS) (var 0))
#eval (List.range 12).map (fun k => (k, (run k [D, var 1, var 2, var 3]).map (fun L => L.length)))
#eval run 7 [D, var 1, var 2, var 3]
#eval run 9 [D, var 1, var 2, var 3]
def exL2 : T := app (app (app S (app S (app S S))) (var 0)) (var 2)
#eval exL2
#eval (run 7 [D, var 1, var 2, var 3]) == some (args (app S (app S S)) ++ var 0 :: var 2 ::
    [app S exL2, app (var 2) exL2, app (app (app S exL2) (app exL2 (app S exL2))) (app (var 2) exL2),
     app (var 1) (var 2), var 3])
