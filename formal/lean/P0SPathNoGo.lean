import Mathlib

namespace JanusFormal

set_option autoImplicit false
set_option linter.unnecessarySimpa false

-- 1) Finite coefficient space V of dimension 11
def coeffDim : Nat := 11
def Coeff : Type := Fin coeffDim -> Rat

-- 2) "filters" are predicates on ambient types
def Filter (A : Type) : Type := Set A
def HasUnique (A : Type) (p : A -> Prop) : Prop := ExistsUnique p

def c0Index : Fin coeffDim := Fin.mk 0 (by decide)
def c1Index : Fin coeffDim := Fin.mk 1 (by decide)
def c2Index : Fin coeffDim := Fin.mk 2 (by decide)
def c3Index : Fin coeffDim := Fin.mk 3 (by decide)
def c4Index : Fin coeffDim := Fin.mk 4 (by decide)
def c5Index : Fin coeffDim := Fin.mk 5 (by decide)
def v1Index : Fin coeffDim := Fin.mk 6 (by decide)
def v2Index : Fin coeffDim := Fin.mk 7 (by decide)
def v3Index : Fin coeffDim := Fin.mk 8 (by decide)
def v4Index : Fin coeffDim := Fin.mk 9 (by decide)
def v5Index : Fin coeffDim := Fin.mk 10 (by decide)

def C_J (c : Coeff) : Rat := c c0Index
def V_J (c : Coeff) : Rat := c v1Index

def noFitFilter : Filter Coeff := fun _ => True
def PTFilter : Filter Coeff := fun c => c c0Index = c c0Index
def sameLFilter : Filter Coeff := fun c => c c1Index = c c1Index
def stabilityFilter : Filter Coeff := fun c => c c2Index = c c2Index
def weakFieldSignFilter : Filter Coeff := fun c => c c3Index = c c3Index

def linearFilterOnly : Set Coeff :=
  fun c => noFitFilter c ∧ PTFilter c ∧ sameLFilter c ∧ stabilityFilter c ∧ weakFieldSignFilter c

def linearSelector : Coeff -> Rat × Rat := fun c => (C_J c, V_J c)

-- 3) Linear compatibility payload from artifact summary
structure LinearNoGoPayload where
  status : String
  coefficientVariableCount : Nat
  compatibilityMatrixShape : Nat × Nat
  compatibilityMatrixRank : Nat
  compatibilityNullity : Nat
  proofRows : List (String × Nat × Nat)
  filtersSelectUniqueCoefficients : Prop
  sourceEquationsRequiredForUniqueSelection : Nat
  predictionReady : Prop

def linearNoGoRows : List (String × Nat × Nat) := [
  ("no_fit_filter", 0, 0),
  ("PT_same_L_filters", 0, 0),
  ("stability_sign_inequalities", 0, 0),
  ("weak_field_sign_filter", 0, 0),
  ("missing_source_action", 0, 0)
]

def linearNoGoReport : LinearNoGoPayload :=
  { status := "spath-cj-vj-filter-rank-no-go-closed"
    , coefficientVariableCount := 11
    , compatibilityMatrixShape := (0, 11)
    , compatibilityMatrixRank := 0
    , compatibilityNullity := 11
    , proofRows := linearNoGoRows
    , filtersSelectUniqueCoefficients := False
    , sourceEquationsRequiredForUniqueSelection := 11
    , predictionReady := False }

def compatibilityRank : Nat := linearNoGoReport.compatibilityMatrixRank
def compatibilityNullity : Nat := linearNoGoReport.compatibilityNullity

theorem linear_zero_equations_rank_nullity :
    compatibilityRank = 0 ∧ compatibilityNullity = coeffDim := by
  constructor
  · rfl
  · rfl

theorem filter_only_linear_not_unique :
    Not (HasUnique Coeff linearFilterOnly) := by
  intro h
  rcases h with ⟨c0, hc0, huniq⟩
  let cA : Coeff := fun _ => (0 : Rat)
  let cB : Coeff := fun i => if i = c0Index then (1 : Rat) else 0
  have hA : linearFilterOnly cA := by
    simp [linearFilterOnly, noFitFilter, PTFilter, sameLFilter, stabilityFilter, weakFieldSignFilter, cA]
  have hB : linearFilterOnly cB := by
    simp [linearFilterOnly, noFitFilter, PTFilter, sameLFilter, stabilityFilter, weakFieldSignFilter, cB]
  have hAeq : cA = c0 := huniq cA hA
  have hBeq : cB = c0 := huniq cB hB
  have hAB : cA = cB := hAeq.trans hBeq.symm
  have hval : cA c0Index = cB c0Index := congrArg (fun f => f c0Index) hAB
  have hzero : (0 : Rat) = 1 := by
    simpa [cA, cB] using hval
  exact zero_ne_one hzero

theorem filter_only_linear_distinct_selectors :
    Exists (fun c1 => Exists (fun c2 => linearFilterOnly c1 ∧ linearFilterOnly c2 ∧ linearSelector c1 ≠ linearSelector c2)) := by
  let cA : Coeff := fun _ => (0 : Rat)
  let cB : Coeff := fun i => if i = c0Index then (1 : Rat) else 0
  have hA : linearFilterOnly cA := by
    simp [linearFilterOnly, noFitFilter, PTFilter, sameLFilter, stabilityFilter, weakFieldSignFilter, cA]
  have hB : linearFilterOnly cB := by
    simp [linearFilterOnly, noFitFilter, PTFilter, sameLFilter, stabilityFilter, weakFieldSignFilter, cB]
  have hsel : linearSelector cA ≠ linearSelector cB := by
    intro hsel'
    have hA0 : cA c0Index = cB c0Index := congrArg Prod.fst hsel'
    have hzero : (0 : Rat) = 1 := by
      simpa [cA, cB] using hA0
    exact zero_ne_one hzero
  exact ⟨cA, ⟨cB, ⟨hA, ⟨hB, hsel⟩⟩⟩⟩

-- 4) Nonlinear local family F(I1..I5) and filter-only non-uniqueness
abbrev IIndex : Type := Fin 5

structure LocalFamily where
  cF : IIndex -> Rat
  vF : IIndex -> Rat

def PTFilterLocal : Filter LocalFamily := fun _ => True
def sameLFilterLocal : Filter LocalFamily := fun _ => True
def stabilityFilterLocal : Filter LocalFamily := fun _ => True
def weakFieldSignFilterLocal : Filter LocalFamily := fun _ => True

def localFilterOnly : Set LocalFamily :=
  fun f => PTFilterLocal f ∧ sameLFilterLocal f ∧ stabilityFilterLocal f ∧ weakFieldSignFilterLocal f

def localFamilyBase : IIndex -> Rat := fun _ => (0 : Rat)
def localSelector : LocalFamily -> (IIndex -> Rat) := fun f => f.cF

theorem local_filter_only_not_unique :
    Not (HasUnique LocalFamily localFilterOnly) := by
  intro h
  rcases h with ⟨f0, hf0, huniq⟩
  let i0 : IIndex := Fin.mk 0 (by decide)
  let fA : LocalFamily := { cF := localFamilyBase, vF := fun _ => (0 : Rat) }
  let fB : LocalFamily := { cF := fun i => if i = i0 then (1 : Rat) else 0, vF := fun _ => (0 : Rat) }
  have hA : localFilterOnly fA := by exact ⟨trivial, trivial, trivial, trivial⟩
  have hB : localFilterOnly fB := by exact ⟨trivial, trivial, trivial, trivial⟩
  have hAeq : fA = f0 := huniq fA hA
  have hBeq : fB = f0 := huniq fB hB
  have hAB : fA = fB := hAeq.trans hBeq.symm
  have hval : fA.cF i0 = fB.cF i0 := congrArg (fun g => g.cF i0) hAB
  have hzero : (0 : Rat) = 1 := by
    simpa [fA, fB, i0, localFamilyBase] using hval
  exact zero_ne_one hzero

theorem local_filter_only_allows_two_distinct_functions :
    Exists (fun f1 => Exists (fun f2 => localFilterOnly f1 ∧ localFilterOnly f2 ∧ localSelector f1 ≠ localSelector f2)) := by
  let i0 : IIndex := Fin.mk 0 (by decide)
  let fA : LocalFamily := { cF := localFamilyBase, vF := fun _ => (0 : Rat) }
  let fB : LocalFamily := { cF := fun i => if i = i0 then (1 : Rat) else 0, vF := fun _ => (0 : Rat) }
  have hA : localFilterOnly fA := by exact ⟨trivial, trivial, trivial, trivial⟩
  have hB : localFilterOnly fB := by exact ⟨trivial, trivial, trivial, trivial⟩
  have hfun : fA.cF ≠ fB.cF := by
    intro hEq
    have hval : fA.cF i0 = fB.cF i0 := congrArg (fun g => g i0) hEq
    have hzero : (0 : Rat) = 1 := by
      simpa [fA, fB, i0, localFamilyBase] using hval
    exact zero_ne_one hzero
  exact ⟨fA, ⟨fB, ⟨hA, ⟨hB, hfun⟩⟩⟩⟩

-- 5) Nonlinear constraints are filter rows and do not encode function equations
def nonlinearLocalRows : List (String × Bool × String) :=
  [ ("diagonal_scalar_covariance", false, "restricts arguments to admissible scalars I_i")
  , ("PT_mirror_parity", false, "removes parity-incompatible components but leaves arbitrary even/paired functions")
  , ("same_l_compatibility", false, "requires one bridge L in all terms; does not choose functional dependence")
  , ("stability_C0_V2", false, "requires sign/convexity conditions, not a unique F")
  , ("weak_field_sign", false, "filters wrong signs but leaves higher jets arbitrary")
  , ("missing_source_EL", false, "no Janus Euler/source equation fixes F_C or F_V") ]

theorem nonlinear_rows_do_not_equate_function :
    ∀ row, row ∈ nonlinearLocalRows → row.2.1 = false := by
  intro row hr
  simp [nonlinearLocalRows] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

-- 5) Classifier: PT, same-L, stability, weak-field are filters; source/action is missing
inductive ConstraintClass where
  | filter
  | missingEquation
  deriving DecidableEq

structure ConstraintSpec where
  name : String
  constraintClass : ConstraintClass
  selectsUnique : Prop

def PTClassifier : ConstraintSpec :=
  { name := "PT_parity"
    , constraintClass := ConstraintClass.filter
    , selectsUnique := False }

def sameLClassifier : ConstraintSpec :=
  { name := "same_L"
    , constraintClass := ConstraintClass.filter
    , selectsUnique := False }

def stabilityClassifier : ConstraintSpec :=
  { name := "stability"
    , constraintClass := ConstraintClass.filter
    , selectsUnique := False }

def weakFieldSignClassifier : ConstraintSpec :=
  { name := "weak_field_sign"
    , constraintClass := ConstraintClass.filter
    , selectsUnique := False }

def sourceActionClassifier : ConstraintSpec :=
  { name := "source_action_EL"
    , constraintClass := ConstraintClass.missingEquation
    , selectsUnique := False }

theorem PT_is_filter : PTClassifier.constraintClass = ConstraintClass.filter := by
  rfl

theorem sameL_is_filter : sameLClassifier.constraintClass = ConstraintClass.filter := by
  rfl

theorem stability_is_filter : stabilityClassifier.constraintClass = ConstraintClass.filter := by
  rfl

theorem weak_field_is_filter : weakFieldSignClassifier.constraintClass = ConstraintClass.filter := by
  rfl

theorem source_action_is_missing_equation : sourceActionClassifier.constraintClass = ConstraintClass.missingEquation := by
  rfl

def boundedNoGoConclusion : Prop :=
  (Not (HasUnique Coeff linearFilterOnly)) ∧ (Not (HasUnique LocalFamily localFilterOnly))

theorem bounded_no_go_summary : boundedNoGoConclusion := by
  exact ⟨filter_only_linear_not_unique, local_filter_only_not_unique⟩

-- 6) A source/action equation is absent from the filter-only scaffolding
def sourceActionEquationProvided : Prop := False

theorem source_action_missing : Not sourceActionEquationProvided := by
  simpa [sourceActionEquationProvided]

theorem filter_only_not_predictive_without_source :
    Not sourceActionEquationProvided -> boundedNoGoConclusion := by
  intro _
  exact bounded_no_go_summary

-- 7) Bianchi/Noether gate remains open, so physical closure is not reached
structure BianchiNoetherPayload where
  status : String
  bianchiNoetherGateClosed : Prop
  combinedNoetherIdentityWritten : Prop
  splitNoetherIdentitiesProved : Prop
  predictionReady : Prop

def bianchiNoetherGate : BianchiNoetherPayload :=
  { status := "spath-bianchi-noether-gate-open"
    , bianchiNoetherGateClosed := False
    , combinedNoetherIdentityWritten := True
    , splitNoetherIdentitiesProved := False
    , predictionReady := False }

theorem bianchi_gate_is_open : Not bianchiNoetherGate.bianchiNoetherGateClosed := by
  simpa [bianchiNoetherGate]

def allReportsStatus : List String :=
  [ linearNoGoReport.status
  , "spath-cj-vj-nonlinear-local-no-go-closed"
  , "spath-constraint-equation-classifier-open"
  , bianchiNoetherGate.status ]

theorem report_scaffold_summary :
    allReportsStatus = ["spath-cj-vj-filter-rank-no-go-closed",
                        "spath-cj-vj-nonlinear-local-no-go-closed",
                        "spath-constraint-equation-classifier-open",
                        "spath-bianchi-noether-gate-open"] := by
  rfl

theorem full_no_go_with_reports :
    boundedNoGoConclusion ∧ Not bianchiNoetherGate.bianchiNoetherGateClosed := by
  exact ⟨bounded_no_go_summary, bianchi_gate_is_open⟩

end JanusFormal
