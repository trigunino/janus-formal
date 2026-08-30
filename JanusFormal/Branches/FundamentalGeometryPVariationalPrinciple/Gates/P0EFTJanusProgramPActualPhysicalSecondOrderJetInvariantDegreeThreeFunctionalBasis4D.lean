import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantCubicFunctionalBasis4D

/-!
# Invariant local functionals of degree at most three

This gate assembles the complete invariant degree-two class with invariant
homogeneous cubics. Evaluation at `x`, `-x`, `2x` and `-2x` separates the odd
linear and cubic parts, making the resulting functional presentation unique.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeThreeFunctionalBasis4D

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
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeTwoFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantCubicFunctionalBasis4D

local instance degreeThreeActualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  actualLLNormedAddCommGroup

local instance degreeThreeActualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  actualLLNormedSpace

local instance degreeThreeActualPhysicalFiniteDimensional :
    FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

private abbrev LinearForm := Fiber →L[Real] Real

private abbrev BilinearForm := Fiber →L[Real] LinearForm

private abbrev TrilinearForm := Fiber →L[Real] BilinearForm

local instance degreeThreeActualPhysicalNormedAddCommGroup :
    NormedAddCommGroup Fiber :=
  inferInstance

local instance degreeThreeActualPhysicalNormedSpace :
    NormedSpace Real Fiber :=
  inferInstance

local instance degreeThreeLinearAddCommGroup :
    AddCommGroup LinearForm :=
  inferInstance

local instance degreeThreeLinearModule :
    Module Real LinearForm :=
  inferInstance

local instance degreeThreeBilinearAddCommGroup :
    AddCommGroup BilinearForm :=
  inferInstance

local instance degreeThreeBilinearModule :
    Module Real BilinearForm :=
  inferInstance

local instance degreeThreeTrilinearAddCommGroup :
    AddCommGroup TrilinearForm :=
  inferInstance

local instance degreeThreeTrilinearModule :
    Module Real TrilinearForm :=
  inferInstance

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev CubicClass :=
  actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod

local instance degreeThreeCubicClassAddCommGroup :
    AddCommGroup (CubicClass period hPeriod) :=
  (actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod).toAddSubgroup.toAddCommGroup

local instance degreeThreeCubicClassModule :
    Module Real (CubicClass period hPeriod) :=
  inferInstance

local instance degreeThreeCubicClassFiniteDimensional :
    FiniteDimensional Real (CubicClass period hPeriod) :=
  actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms_finiteDimensional
    period hPeriod

/-- Complete invariant local-functional data of polynomial degree at most
three. -/
@[ext]
structure ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional where
  lower : ActualPhysicalSecondOrderJetInvariantDegreeTwoFunctional period hPeriod
  cubic : CubicClass period hPeriod

/-- Complete scalar coefficients of an invariant degree-three functional. -/
@[ext]
structure ActualPhysicalSecondOrderJetInvariantDegreeThreeCoefficients where
  lower : ActualPhysicalSecondOrderJetInvariantDegreeTwoCoefficients period hPeriod
  cubic : ActualPhysicalSecondOrderJetInvariantCubicFunctionalIndex period hPeriod → Real

/-- Evaluation of the lower-degree and homogeneous cubic components. -/
def actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional period hPeriod)
    (jet : Fiber) : Real :=
  actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation period hPeriod
      functional.lower jet +
    actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod
      functional.cubic jet

/-- Every classified degree-three functional is fixed by every genuine
second-jet transition. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation_transitionInvariant
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional period hPeriod)
    (first second : ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod))
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation period hPeriod
        functional
        ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base jet) =
      actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation period hPeriod
        functional jet := by
  unfold actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation
  rw [actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation_transitionInvariant
    period hPeriod functional.lower first second base hBase jet]
  rw [actualPhysicalSecondOrderJetInvariantCubicEvaluation_transitionInvariant
    period hPeriod functional.cubic first second base hBase jet]

/-- Equality of evaluated degree-three functions forces equality of every
lower-degree and cubic component. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation_injective :
    Function.Injective
      (fun functional :
          ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional period hPeriod =>
        actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation period hPeriod
          functional) := by
  intro firstFunctional secondFunctional hEvaluation
  have hCubicPointwise :
      ∀ jet : Fiber,
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod
            firstFunctional.cubic jet =
          actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod
            secondFunctional.cubic jet := by
    intro jet
    have hPositive := congrFun hEvaluation jet
    have hNegative := congrFun hEvaluation (-jet)
    have hDouble := congrFun hEvaluation ((2 : Real) • jet)
    have hNegativeDouble := congrFun hEvaluation (-((2 : Real) • jet))
    simp only [actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
      actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
      actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
      actualPhysicalSecondOrderJetInvariantCubicEvaluation, map_neg, neg_apply,
      neg_neg, map_smul, smul_apply, smul_eq_mul] at hNegative hDouble hNegativeDouble
    dsimp [actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
      actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
      actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
      actualPhysicalSecondOrderJetInvariantCubicEvaluation] at hPositive
    change firstFunctional.cubic.1 jet jet jet =
      secondFunctional.cubic.1 jet jet jet
    linarith
  have hCubicEvaluation :
      actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod
          firstFunctional.cubic =
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod
          secondFunctional.cubic := by
    funext jet
    exact hCubicPointwise jet
  have hCubic : firstFunctional.cubic = secondFunctional.cubic :=
    actualPhysicalSecondOrderJetInvariantCubicEvaluation_injective period hPeriod
      hCubicEvaluation
  have hLowerEvaluation :
      actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation period hPeriod
          firstFunctional.lower =
        actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation period hPeriod
          secondFunctional.lower := by
    funext jet
    have hAtJet := congrFun hEvaluation jet
    have hCubicAtJet := congrArg
      (fun cubic : CubicClass period hPeriod =>
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod cubic jet)
      hCubic
    dsimp [actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation] at hAtJet
    linarith
  have hLower : firstFunctional.lower = secondFunctional.lower :=
    actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation_injective period hPeriod
      hLowerEvaluation
  cases firstFunctional
  cases secondFunctional
  cases hLower
  cases hCubic
  rfl

/-- Complete scalar coordinates of an invariant degree-three functional. -/
def actualPhysicalSecondOrderJetInvariantDegreeThreeCoordinates
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional period hPeriod) :
    ActualPhysicalSecondOrderJetInvariantDegreeThreeCoefficients period hPeriod where
  lower := actualPhysicalSecondOrderJetInvariantDegreeTwoCoordinates period hPeriod
    functional.lower
  cubic := actualPhysicalSecondOrderJetInvariantCubicFunctionalCoordinateEquiv
    period hPeriod functional.cubic

/-- Synthesis from all scalar coefficients through degree three. -/
def actualPhysicalSecondOrderJetInvariantDegreeThreeSynthesis
    (coefficients :
      ActualPhysicalSecondOrderJetInvariantDegreeThreeCoefficients period hPeriod) :
    ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional period hPeriod where
  lower := actualPhysicalSecondOrderJetInvariantDegreeTwoSynthesis period hPeriod
    coefficients.lower
  cubic := (actualPhysicalSecondOrderJetInvariantCubicFunctionalCoordinateEquiv
    period hPeriod).symm coefficients.cubic

/-- Scalar-coordinate synthesis through degree three is injective. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeThreeSynthesis_injective :
    Function.Injective
      (actualPhysicalSecondOrderJetInvariantDegreeThreeSynthesis period hPeriod) := by
  intro firstCoefficients secondCoefficients hSynthesis
  apply ActualPhysicalSecondOrderJetInvariantDegreeThreeCoefficients.ext
  · apply actualPhysicalSecondOrderJetInvariantDegreeTwoSynthesis_injective
      period hPeriod
    exact congrArg
      ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional.lower hSynthesis
  · apply (actualPhysicalSecondOrderJetInvariantCubicFunctionalCoordinateEquiv
      period hPeriod).symm.injective
    exact congrArg
      ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional.cubic hSynthesis

/-- Synthesis reconstructs every invariant degree-three functional exactly. -/
@[simp]
theorem actualPhysicalSecondOrderJetInvariantDegreeThree_reconstruction
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional period hPeriod) :
    actualPhysicalSecondOrderJetInvariantDegreeThreeSynthesis period hPeriod
        (actualPhysicalSecondOrderJetInvariantDegreeThreeCoordinates period hPeriod
          functional) =
      functional := by
  cases functional
  simp [actualPhysicalSecondOrderJetInvariantDegreeThreeSynthesis,
    actualPhysicalSecondOrderJetInvariantDegreeThreeCoordinates]

/-- Every invariant local functional of degree at most three has one and only
one complete scalar coefficient family. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeThree_existsUnique_coefficients
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional period hPeriod) :
    ∃! coefficients :
        ActualPhysicalSecondOrderJetInvariantDegreeThreeCoefficients period hPeriod,
      actualPhysicalSecondOrderJetInvariantDegreeThreeSynthesis period hPeriod
          coefficients = functional := by
  refine ⟨actualPhysicalSecondOrderJetInvariantDegreeThreeCoordinates period hPeriod
      functional, actualPhysicalSecondOrderJetInvariantDegreeThree_reconstruction
        period hPeriod functional, ?_⟩
  intro coefficients hCoefficients
  apply actualPhysicalSecondOrderJetInvariantDegreeThreeSynthesis_injective
    period hPeriod
  exact hCoefficients.trans
    (actualPhysicalSecondOrderJetInvariantDegreeThree_reconstruction
      period hPeriod functional).symm

end
end P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeThreeFunctionalBasis4D
end JanusFormal
