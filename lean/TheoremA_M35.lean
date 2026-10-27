/-
  Theorem A in Lean, bignum-table version (main agent, 2026-10-27): the 35-class head-normalisation model M35 (data/model35_hn.txt,
  isomorphic to BEKW's Fig. 14 automaton) is an S-model, so its class is invariant along head runs; every head
  normal form has a class in F. Hence a term whose class is not in F has no head normal form.
  Table generated mechanically from the data file by the main agent.
-/
inductive Tm where
  | S : Tm
  | app : Tm → Tm → Tm
deriving DecidableEq, Repr

open Tm

def args : Tm → List Tm
  | S => []
  | app f x => args f ++ [x]

def step : List Tm → Option (List Tm)
  | a :: b :: c :: R => some (args a ++ c :: app b c :: R)
  | _ => none

def run : Nat → List Tm → Option (List Tm)
  | 0, L => some L
  | k + 1, L => match step L with
    | some L' => run k L'
    | none => none

/-- the 35×35 product table as one natural number in base 35: entry (a, b) is digit 35·a + b -/
def TAB : Nat := 29538562191222620684320081899232842754670124900736763521668000729659287016484259335777889864422233901003611783465599855032323383667755269420523759846519407854326214244162200860261196204000983879465662862832812775281344614718350186660573389708754516866372087215350870174000213278538077694110585211888178172706056721317482125610032683220213626728259322667353060652718214409224115522991113186537593708345029105242327648458214379292939798631848921310119363597816348469279020180791198610003744392392901307059015429206808428354540786935115615555061783711294488670470326231511218015678171818108176776943925270929866538499919971789818934443981551320637978833001705049973587030890054513712659855835716452940024406619597766549226623935781543408038004226553639607523884562123333550690589702291805396433048256791960158474157557365988870480690494748230588715975753321649585450152853881788364956380281134208407796440733142308667468718098111196350610373242444622816547151418208095524161062588592677666257332809567134410314084977008085233188236718777234280745084495384213545038942153947465549217993168372871271532948861225719492399369040255731624612720899661474300527210494970976593169841460465756385570205955652957906827453723671819872918761939099295683061463436555090746110169410912891406358250922428953318536926493793823622782846021366858806738075492721479046397598310460940246273842607026519842627223866954999276883472332251139319203658014930738531082985299529881001571362642615441576854794458396830031814694899369128396346637595812026675343631597149506625133631298743193719461115279095950536034727357272892666353045584141367514524685946919355026384905978555932774652568711436145597909898990598687846064663905630806526514253443258246434921630690124204508490850547161589236504794240645475217674535395073940646302304849950070696700364764388501843967855393986215504971523726643875387395129321038634680311846

def mul (a b : Nat) : Nat := (TAB / 35 ^ (35 * a + b)) % 35

/-- the F classes as a bit mask -/
def FMASK : Nat := 25769803775
def isF (k : Nat) : Bool := (FMASK / 2 ^ k) % 2 == 1

def cls : Tm → Nat
  | S => 0
  | app f x => mul (cls f) (cls x)

/-- class of the term S·L1·L2·… -/
def clsL (L : List Tm) : Nat := L.foldl (fun acc t => mul acc (cls t)) 0

/-- (F1) the S-identity, as one Boolean check over all 35³ class triples -/
def checkS : Bool := (List.range 35).all fun x => (List.range 35).all fun y => (List.range 35).all fun z =>
  mul (mul (mul 0 x) y) z == mul (mul x z) (mul y z)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem checkS_true : checkS = true := by decide +kernel

/-- every product is a class index below 35 -/
def checkRange : Bool := (List.range 35).all fun x => (List.range 35).all fun y => mul x y < 35

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem checkRange_true : checkRange = true := by decide +kernel

theorem s_identity (x y z : Nat) (hx : x < 35) (hy : y < 35) (hz : z < 35) :
    mul (mul (mul 0 x) y) z = mul (mul x z) (mul y z) := by
  have h := checkS_true
  simp only [checkS, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h x hx y hy z hz

/-- (F1') hnf shapes S, S x, S x y land in F -/
def checkH : Bool := isF 0 && (List.range 35).all (fun x => isF (mul 0 x)) &&
  (List.range 35).all fun x => (List.range 35).all fun y => isF (mul (mul 0 x) y)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem checkH_true : checkH = true := by decide +kernel

theorem cls_lt : ∀ t : Tm, cls t < 35
  | S => by simp [cls]
  | app f x => by
    have h := checkRange_true
    simp only [checkRange, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h _ (cls_lt f) _ (cls_lt x)

theorem foldl_lt (L : List Tm) (acc : Nat) (h : acc < 35) : L.foldl (fun acc t => mul acc (cls t)) acc < 35 := by
  induction L generalizing acc with
  | nil => simpa using h
  | cons t L ih =>
    simp only [List.foldl]
    apply ih
    have hr := checkRange_true
    simp only [checkRange, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hr
    exact hr _ h _ (cls_lt t)

theorem clsL_lt (L : List Tm) : clsL L < 35 := foldl_lt L 0 (by decide)

/-- the class of a term is the class of S applied to its argument list -/
theorem cls_args : ∀ t : Tm, cls t = clsL (args t)
  | S => by simp [cls, clsL, args]
  | app f x => by
    simp only [cls, clsL, args, List.foldl_append, List.foldl]
    rw [cls_args f]; rfl

/-- (Lemma 3) the class is invariant along a head step -/
theorem clsL_step (L L' : List Tm) (h : step L = some L') : clsL L = clsL L' := by
  match L, h with
  | a :: b :: c :: R, h =>
    simp only [step, Option.some.injEq] at h
    subst h
    simp only [clsL, List.foldl_append, List.foldl]
    have e : (args a).foldl (fun acc t => mul acc (cls t)) 0 = cls a := (cls_args a).symm
    rw [e, s_identity (cls a) (cls b) (cls c) (cls_lt a) (cls_lt b) (cls_lt c)]
    rfl

theorem clsL_run : ∀ (n : Nat) (L L' : List Tm), run n L = some L' → clsL L = clsL L'
  | 0, L, L', h => by simp [run] at h; subst h; rfl
  | n + 1, L, L', h => by
    simp only [run] at h
    cases hs : step L with
    | none => rw [hs] at h; simp at h
    | some L1 => rw [hs] at h; exact (clsL_step L L1 hs).trans (clsL_run n L1 L' h)

/-- every head normal form (a list of length <= 2) has its class in F -/
theorem hnf_inF (L : List Tm) (h : L.length ≤ 2) : isF (clsL L) = true := by
  have hh := checkH_true
  simp only [checkH, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hh
  obtain ⟨⟨h0, h1⟩, h2⟩ := hh
  match L, h with
  | [], _ => simpa [clsL] using h0
  | [x], _ => simpa [clsL] using h1 (cls x) (cls_lt x)
  | [x, y], _ => simpa [clsL] using h2 (cls x) (cls_lt x) (cls y) (cls_lt y)

/-- **Theorem A.** If the class of S·L is not in F, the head run from L never reaches a head normal form. -/
theorem theoremA (L : List Tm) (hF : isF (clsL L) = false) :
    ∀ n L', run n L = some L' → 3 ≤ L'.length := by
  intro n L' hr
  rcases Nat.lt_or_ge L'.length 3 with hlt | hge
  · exfalso
    have h2 : L'.length ≤ 2 := by omega
    have := hnf_inF L' h2
    rw [← clsL_run n L L' hr, hF] at this
    exact Bool.false_ne_true this
  · exact hge

#print axioms checkS_true
#print axioms s_identity
#print axioms checkH_true
#print axioms theoremA
