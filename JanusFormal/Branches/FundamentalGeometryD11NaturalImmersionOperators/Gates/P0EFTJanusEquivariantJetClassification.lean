import Mathlib

namespace JanusFormal
namespace P0EFTJanusEquivariantJetClassification

set_option autoImplicit false

universe u v w

/-- Abstract action of a symmetry object on a fiber. -/
structure ActionData (Symmetry : Type u) (Fiber : Type v) where
  act : Symmetry → Fiber → Fiber

/-- Equivariant map between two action fibers. -/
structure EquivariantMap
    {Symmetry : Type u}
    {Source : Type v}
    {Target : Type w}
    (sourceAction : ActionData Symmetry Source)
    (targetAction : ActionData Symmetry Target) where
  toFun : Source → Target
  equivariant :
    ∀ symmetry source,
      toFun (sourceAction.act symmetry source) =
        targetAction.act symmetry (toFun source)

/-- Identity equivariant map. -/
def identityEquivariantMap
    {Symmetry : Type u}
    {Fiber : Type v}
    (action : ActionData Symmetry Fiber) :
    EquivariantMap action action where
  toFun := fun value => value
  equivariant := by
    intro symmetry value
    rfl

/-- Composition of equivariant maps. -/
def composeEquivariantMaps
    {Symmetry : Type u}
    {First : Type v}
    {Second : Type w}
    {Third : Type*}
    (firstAction : ActionData Symmetry First)
    (secondAction : ActionData Symmetry Second)
    (thirdAction : ActionData Symmetry Third)
    (secondMap : EquivariantMap secondAction thirdAction)
    (firstMap : EquivariantMap firstAction secondAction) :
    EquivariantMap firstAction thirdAction where
  toFun := fun value => secondMap.toFun (firstMap.toFun value)
  equivariant := by
    intro symmetry value
    rw [firstMap.equivariant, secondMap.equivariant]

/-- Trivial action. -/
def trivialAction
    (Symmetry : Type u)
    (Fiber : Type v) : ActionData Symmetry Fiber where
  act := fun _ value => value

/-- Every map between trivial actions is equivariant. -/
def equivariantMapOfTrivialActions
    {Symmetry : Type u}
    {Source : Type v}
    {Target : Type w}
    (map : Source → Target) :
    EquivariantMap
      (trivialAction Symmetry Source)
      (trivialAction Symmetry Target) where
  toFun := map
  equivariant := by
    intro symmetry source
    rfl

/-- Order-`k` jet representation at one standard model fiber. -/
structure JetRepresentationProblem where
  Symmetry : Type u
  JetFiber : Type v
  TargetFiber : Type w
  jetAction : ActionData Symmetry JetFiber
  targetAction : ActionData Symmetry TargetFiber

/-- Candidate natural operator in the finite-jet classification. -/
abbrev ClassifiedJetOperator
    (problem : JetRepresentationProblem) :=
  EquivariantMap problem.jetAction problem.targetAction

/-- Multiplicity-one/subsingleton criterion for uniqueness. -/
def JetOperatorUnique
    (problem : JetRepresentationProblem) : Prop :=
  Subsingleton (ClassifiedJetOperator problem)

/-- Under the multiplicity-one criterion, any two classified operators agree. -/
theorem classified_operator_unique
    (problem : JetRepresentationProblem)
    (hUnique : JetOperatorUnique problem)
    (first second : ClassifiedJetOperator problem) :
    first = second := by
  exact @Subsingleton.elim _ hUnique first second

/-- Trivial one-dimensional jet problem. -/
def trivialRealJetProblem : JetRepresentationProblem where
  Symmetry := Unit
  JetFiber := ℝ
  TargetFiber := ℝ
  jetAction := trivialAction Unit ℝ
  targetAction := trivialAction Unit ℝ

/-- Scalar multiplication gives an equivariant operator in the trivial problem. -/
def scalarJetOperator
    (coefficient : ℝ) :
    ClassifiedJetOperator trivialRealJetProblem :=
  equivariantMapOfTrivialActions
    (Symmetry := Unit)
    (fun value : ℝ => coefficient * value)

/-- Distinct coefficients give distinct natural jet operators. -/
theorem scalar_jet_operators_distinct
    (first second : ℝ)
    (hDistinct : first ≠ second) :
    scalarJetOperator first ≠ scalarJetOperator second := by
  intro hEqual
  have hAtOne := congrArg
    (fun operator => operator.toFun 1) hEqual
  simp [scalarJetOperator] at hAtOne
  exact hDistinct hAtOne

/-- The trivial jet problem is not uniquely classified. -/
theorem trivial_real_jet_problem_not_unique :
    Not (JetOperatorUnique trivialRealJetProblem) := by
  intro hUnique
  exact scalar_jet_operators_distinct 0 1 (by norm_num)
    (@Subsingleton.elim _ hUnique
      (scalarJetOperator 0) (scalarJetOperator 1))

/-- Abstract reduction of a regular local natural operator to an equivariant jet map. -/
structure NaturalToJetClassificationStatus where
  finiteOrder : ℕ
  modelFiberChosen : Prop
  structureGroupIdentified : Prop
  sourceJetRepresentationConstructed : Prop
  targetRepresentationConstructed : Prop
  coordinateIndependenceProved : Prop
  naturalOperatorMappedToEquivariantJetMap : Prop
  equivariantJetMapReconstructsNaturalOperator : Prop
  classificationBijectionProved : Prop

/-- A full classification theorem. -/
def naturalToJetClassificationClosed
    (s : NaturalToJetClassificationStatus) : Prop :=
  s.modelFiberChosen /\
  s.structureGroupIdentified /\
  s.sourceJetRepresentationConstructed /\
  s.targetRepresentationConstructed /\
  s.coordinateIndependenceProved /\
  s.naturalOperatorMappedToEquivariantJetMap /\
  s.equivariantJetMapReconstructsNaturalOperator /\
  s.classificationBijectionProved

/-- Uniqueness requires a representation-theoretic multiplicity theorem. -/
structure NaturalOperatorUniquenessStatus where
  jetClassificationProved : Prop
  equivariantOperatorSpaceComputed : Prop
  multiplicityOneProved : Prop
  normalizationFixed : Prop
  lowerOrderCountertermsExcludedOrFixed : Prop
  uniqueNaturalOperatorDerived : Prop


def naturalOperatorUniquenessClosed
    (s : NaturalOperatorUniquenessStatus) : Prop :=
  s.jetClassificationProved /\
  s.equivariantOperatorSpaceComputed /\
  s.multiplicityOneProved /\
  s.normalizationFixed /\
  s.lowerOrderCountertermsExcludedOrFixed /\
  s.uniqueNaturalOperatorDerived

/-- Missing multiplicity one blocks a uniqueness claim. -/
theorem missing_multiplicity_one_blocks_uniqueness
    (s : NaturalOperatorUniquenessStatus)
    (hMissing : Not s.multiplicityOneProved) :
    Not (naturalOperatorUniquenessClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.1

/--
This module is the finite-dimensional invariant-theory core of D11.  The
Peetre--Slovak theorem supplies finite jets; equivariance under the relevant
jet/structure group then classifies the natural operators.  Bare naturality
alone never implies uniqueness.
-/
structure JanusJetInvariantTheoryStatus where
  spinCJetGroupIdentified : Prop
  immersionJetVariablesIdentified : Prop
  normalRootRepresentationIncluded : Prop
  monopoleRepresentationIncluded : Prop
  tensorAndGhostRepresentationsIncluded : Prop
  equivariantHomSpacesComputed : Prop
  canonicalSymbolsLocated : Prop
  lowerOrderInvariantBasisComputed : Prop
  multiplicitiesAndFreeCouplingsReported : Prop


def janusJetInvariantTheoryClosed
    (s : JanusJetInvariantTheoryStatus) : Prop :=
  s.spinCJetGroupIdentified /\
  s.immersionJetVariablesIdentified /\
  s.normalRootRepresentationIncluded /\
  s.monopoleRepresentationIncluded /\
  s.tensorAndGhostRepresentationsIncluded /\
  s.equivariantHomSpacesComputed /\
  s.canonicalSymbolsLocated /\
  s.lowerOrderInvariantBasisComputed /\
  s.multiplicitiesAndFreeCouplingsReported

end P0EFTJanusEquivariantJetClassification
end JanusFormal
