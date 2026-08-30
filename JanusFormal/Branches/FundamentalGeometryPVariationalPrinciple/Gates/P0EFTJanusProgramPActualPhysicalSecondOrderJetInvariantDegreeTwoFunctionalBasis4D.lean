import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis4D

/-!
# Invariant local functionals of degree at most two

This gate assembles constants, invariant bounded linear functionals and
invariant homogeneous quadratic functionals into one exhaustive degree-two
class.  Its scalar coefficient families and its evaluation as a function on
the actual physical second-jet fiber are both unique.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeTwoFunctionalBasis4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open Set
open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis4D

local instance degreeTwoActualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  actualLLNormedAddCommGroup

local instance degreeTwoActualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  actualLLNormedSpace

local instance degreeTwoActualPhysicalFiniteDimensional :
    FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

private abbrev BilinearForm := Fiber →L[Real] Fiber →L[Real] Real

local instance degreeTwoActualPhysicalNormedAddCommGroup :
    NormedAddCommGroup Fiber :=
  inferInstance

local instance degreeTwoActualPhysicalNormedSpace :
    NormedSpace Real Fiber :=
  inferInstance

local instance degreeTwoDualAddCommGroup :
    AddCommGroup (Fiber →L[Real] Real) :=
  inferInstance

local instance degreeTwoDualModule :
    Module Real (Fiber →L[Real] Real) :=
  inferInstance

local instance degreeTwoBilinearAddCommGroup :
    AddCommGroup BilinearForm :=
  inferInstance

local instance degreeTwoBilinearModule :
    Module Real BilinearForm :=
  inferInstance

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev LinearClass :=
  actualPhysicalSecondOrderJetTransitionInvariantFunctionals period hPeriod

private abbrev QuadraticClass :=
  actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod

local instance degreeTwoLinearClassAddCommGroup :
    AddCommGroup (LinearClass period hPeriod) :=
  (actualPhysicalSecondOrderJetTransitionInvariantFunctionals period hPeriod).toAddSubgroup.toAddCommGroup

local instance degreeTwoLinearClassModule :
    Module Real (LinearClass period hPeriod) :=
  inferInstance

local instance degreeTwoLinearClassFiniteDimensional :
    FiniteDimensional Real (LinearClass period hPeriod) :=
  actualPhysicalSecondOrderJetTransitionInvariantFunctionals_finiteDimensional
    period hPeriod

local instance degreeTwoQuadraticClassAddCommGroup :
    AddCommGroup (QuadraticClass period hPeriod) :=
  (actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod).toAddSubgroup.toAddCommGroup

local instance degreeTwoQuadraticClassModule :
    Module Real (QuadraticClass period hPeriod) :=
  inferInstance

local instance degreeTwoQuadraticClassFiniteDimensional :
    FiniteDimensional Real (QuadraticClass period hPeriod) :=
  actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms_finiteDimensional
    period hPeriod

/-- A complete invariant local functional presentation of polynomial degree at
most two. -/
@[ext]
structure ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional where
  constant : Real
  linear : LinearClass period hPeriod
  quadratic : QuadraticClass period hPeriod

/-- Scalar coordinates for every component of an invariant degree-two
functional. -/
@[ext]
structure ActualPhysicalSecondOrderJetInvariantDegreeTwoCoefficients where
  constant : Real
  linear : ActualPhysicalSecondOrderJetInvariantFunctionalIndex period hPeriod → Real
  quadratic :
    ActualPhysicalSecondOrderJetInvariantQuadraticFunctionalIndex period hPeriod → Real

/-- Evaluation of the classified constant, linear and quadratic components. -/
def actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional period hPeriod)
    (jet : Fiber) : Real :=
  functional.constant + functional.linear.1 jet +
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation period hPeriod
      functional.quadratic jet

/-- Every classified degree-two functional is fixed by all genuine second-jet
transitions. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation_transitionInvariant
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional period hPeriod)
    (first second : ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod))
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation period hPeriod functional
        ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base jet) =
      actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation period hPeriod
        functional jet := by
  unfold actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation
  rw [functional.linear.property first second base hBase jet]
  rw [actualPhysicalSecondOrderJetInvariantQuadraticEvaluation_transitionInvariant
    period hPeriod functional.quadratic first second base hBase jet]

/-- Evaluation is injective: equality as functions forces equality of the
constant, linear and symmetric-bilinear components. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation_injective :
    Function.Injective
      (fun functional :
          ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional period hPeriod =>
        actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation period hPeriod
          functional) := by
  intro firstFunctional secondFunctional hEvaluation
  have hConstant : firstFunctional.constant = secondFunctional.constant := by
    have hZero := congrFun hEvaluation (0 : Fiber)
    simpa [actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
      actualPhysicalSecondOrderJetInvariantQuadraticEvaluation] using hZero
  have hLinearPointwise :
      ∀ jet : Fiber, firstFunctional.linear.1 jet = secondFunctional.linear.1 jet := by
    intro jet
    have hPositive := congrFun hEvaluation jet
    have hNegative := congrFun hEvaluation (-jet)
    simp only [actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
      actualPhysicalSecondOrderJetInvariantQuadraticEvaluation, map_neg, neg_apply,
      neg_neg] at hNegative
    dsimp [actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
      actualPhysicalSecondOrderJetInvariantQuadraticEvaluation] at hPositive
    linarith
  have hLinear : firstFunctional.linear = secondFunctional.linear := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    exact hLinearPointwise
  have hQuadraticEvaluation :
      actualPhysicalSecondOrderJetInvariantQuadraticEvaluation period hPeriod
          firstFunctional.quadratic =
        actualPhysicalSecondOrderJetInvariantQuadraticEvaluation period hPeriod
          secondFunctional.quadratic := by
    funext jet
    have hAtJet := congrFun hEvaluation jet
    have hLinearAtJet := congrArg (fun linear : LinearClass period hPeriod => linear.1 jet)
      hLinear
    dsimp [actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation] at hAtJet
    linarith
  have hQuadratic : firstFunctional.quadratic = secondFunctional.quadratic :=
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation_injective period hPeriod
      hQuadraticEvaluation
  cases firstFunctional
  cases secondFunctional
  cases hConstant
  cases hLinear
  cases hQuadratic
  rfl

/-- Complete scalar coordinates of an invariant degree-two functional. -/
def actualPhysicalSecondOrderJetInvariantDegreeTwoCoordinates
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional period hPeriod) :
    ActualPhysicalSecondOrderJetInvariantDegreeTwoCoefficients period hPeriod where
  constant := functional.constant
  linear := actualPhysicalSecondOrderJetInvariantFunctionalCoordinateEquiv
    period hPeriod functional.linear
  quadratic := actualPhysicalSecondOrderJetInvariantQuadraticFunctionalCoordinateEquiv
    period hPeriod functional.quadratic

/-- Synthesis from the complete constant, linear and quadratic scalar
coefficients. -/
def actualPhysicalSecondOrderJetInvariantDegreeTwoSynthesis
    (coefficients :
      ActualPhysicalSecondOrderJetInvariantDegreeTwoCoefficients period hPeriod) :
    ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional period hPeriod where
  constant := coefficients.constant
  linear := (actualPhysicalSecondOrderJetInvariantFunctionalCoordinateEquiv
    period hPeriod).symm coefficients.linear
  quadratic :=
    (actualPhysicalSecondOrderJetInvariantQuadraticFunctionalCoordinateEquiv
      period hPeriod).symm coefficients.quadratic

/-- Scalar-coordinate synthesis is injective. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeTwoSynthesis_injective :
    Function.Injective
      (actualPhysicalSecondOrderJetInvariantDegreeTwoSynthesis period hPeriod) := by
  intro firstCoefficients secondCoefficients hSynthesis
  apply ActualPhysicalSecondOrderJetInvariantDegreeTwoCoefficients.ext
  · exact congrArg
      ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional.constant hSynthesis
  · apply (actualPhysicalSecondOrderJetInvariantFunctionalCoordinateEquiv
      period hPeriod).symm.injective
    exact congrArg
      ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional.linear hSynthesis
  · apply (actualPhysicalSecondOrderJetInvariantQuadraticFunctionalCoordinateEquiv
      period hPeriod).symm.injective
    exact congrArg
      ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional.quadratic hSynthesis

/-- Synthesis reconstructs every invariant degree-two functional exactly. -/
@[simp]
theorem actualPhysicalSecondOrderJetInvariantDegreeTwo_reconstruction
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional period hPeriod) :
    actualPhysicalSecondOrderJetInvariantDegreeTwoSynthesis period hPeriod
        (actualPhysicalSecondOrderJetInvariantDegreeTwoCoordinates period hPeriod
          functional) =
      functional := by
  cases functional
  simp [actualPhysicalSecondOrderJetInvariantDegreeTwoSynthesis,
    actualPhysicalSecondOrderJetInvariantDegreeTwoCoordinates]

/-- Every invariant local functional of degree at most two has one and only one
complete scalar coefficient family. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeTwo_existsUnique_coefficients
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional period hPeriod) :
    ∃! coefficients :
        ActualPhysicalSecondOrderJetInvariantDegreeTwoCoefficients period hPeriod,
      actualPhysicalSecondOrderJetInvariantDegreeTwoSynthesis period hPeriod
          coefficients = functional := by
  refine ⟨actualPhysicalSecondOrderJetInvariantDegreeTwoCoordinates period hPeriod
      functional, actualPhysicalSecondOrderJetInvariantDegreeTwo_reconstruction
        period hPeriod functional, ?_⟩
  intro coefficients hCoefficients
  apply actualPhysicalSecondOrderJetInvariantDegreeTwoSynthesis_injective
    period hPeriod
  exact hCoefficients.trans
    (actualPhysicalSecondOrderJetInvariantDegreeTwo_reconstruction
      period hPeriod functional).symm

end
end P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeTwoFunctionalBasis4D
end JanusFormal
