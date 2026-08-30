import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis4D

/-!
# Invariant local functionals of degree at most four

This gate assembles the complete invariant degree-three class with invariant
homogeneous quartics. Even evaluation at `x`, `-x`, `2x`, `-2x` and `0`
separates the quadratic and quartic parts.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D

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
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeThreeFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis4D

local instance degreeFourActualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  actualLLNormedAddCommGroup

local instance degreeFourActualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  actualLLNormedSpace

local instance degreeFourActualPhysicalFiniteDimensional :
    FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

private abbrev LinearForm := Fiber →L[Real] Real

private abbrev BilinearForm := Fiber →L[Real] LinearForm

private abbrev TrilinearForm := Fiber →L[Real] BilinearForm

local instance degreeFourActualPhysicalNormedAddCommGroup :
    NormedAddCommGroup Fiber := inferInstance

local instance degreeFourActualPhysicalNormedSpace :
    NormedSpace Real Fiber := inferInstance

local instance degreeFourLinearNormedAddCommGroup :
    NormedAddCommGroup LinearForm := inferInstance
local instance degreeFourLinearNormedSpace :
    NormedSpace Real LinearForm := inferInstance
local instance degreeFourBilinearNormedAddCommGroup :
    NormedAddCommGroup BilinearForm := inferInstance
local instance degreeFourBilinearNormedSpace :
    NormedSpace Real BilinearForm := inferInstance
local instance degreeFourTrilinearNormedAddCommGroup :
    NormedAddCommGroup TrilinearForm := inferInstance
local instance degreeFourTrilinearNormedSpace :
    NormedSpace Real TrilinearForm := inferInstance

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev QuarticClass :=
  actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod

local instance degreeFourQuarticClassAddCommGroup :
    AddCommGroup (QuarticClass period hPeriod) :=
  (actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period
    hPeriod).toAddSubgroup.toAddCommGroup

local instance degreeFourQuarticClassModule :
    Module Real (QuarticClass period hPeriod) := inferInstance

/-- Complete invariant local-functional data of polynomial degree at most
four. -/
@[ext]
structure ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional where
  lower : ActualPhysicalSecondOrderJetInvariantDegreeThreeFunctional period hPeriod
  quartic : QuarticClass period hPeriod

/-- Complete scalar coefficients of an invariant degree-four functional. -/
@[ext]
structure ActualPhysicalSecondOrderJetInvariantDegreeFourCoefficients where
  lower : ActualPhysicalSecondOrderJetInvariantDegreeThreeCoefficients period hPeriod
  quartic : ActualPhysicalSecondOrderJetInvariantQuarticFunctionalIndex period hPeriod → Real

/-- Evaluation of the lower-degree and homogeneous quartic components. -/
def actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod)
    (jet : Fiber) : Real :=
  actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation period hPeriod
      functional.lower jet +
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod
      functional.quartic jet

/-- Every classified degree-four functional is fixed by every genuine
second-jet transition. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation_transitionInvariant
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod)
    (first second : ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod))
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        functional
        ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base jet) =
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        functional jet := by
  unfold actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation
  rw [actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation_transitionInvariant
    period hPeriod functional.lower first second base hBase jet]
  rw [actualPhysicalSecondOrderJetInvariantQuarticEvaluation_transitionInvariant
    period hPeriod functional.quartic first second base hBase jet]

/-- Equality of evaluated degree-four functions forces equality of every
lower-degree and quartic component. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation_injective :
    Function.Injective
      (fun functional :
          ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod =>
        actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
          functional) := by
  intro firstFunctional secondFunctional hEvaluation
  have hQuarticPointwise : ∀ jet : Fiber,
      actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod
          firstFunctional.quartic jet =
        actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod
          secondFunctional.quartic jet := by
    intro jet
    have hZero := congrFun hEvaluation (0 : Fiber)
    have hPositive := congrFun hEvaluation jet
    have hNegative := congrFun hEvaluation (-jet)
    have hDouble := congrFun hEvaluation ((2 : Real) • jet)
    have hNegativeDouble := congrFun hEvaluation (-((2 : Real) • jet))
    simp only [actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation,
      actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
      actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
      actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
      actualPhysicalSecondOrderJetInvariantCubicEvaluation,
      actualPhysicalSecondOrderJetInvariantQuarticEvaluation, map_zero,
      add_zero, map_neg, neg_apply, neg_neg, map_smul, smul_apply,
      smul_eq_mul] at hZero hNegative hDouble hNegativeDouble
    dsimp [actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation,
      actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
      actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
      actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
      actualPhysicalSecondOrderJetInvariantCubicEvaluation,
      actualPhysicalSecondOrderJetInvariantQuarticEvaluation] at hPositive
    change firstFunctional.quartic.1 jet jet jet jet =
      secondFunctional.quartic.1 jet jet jet jet
    linarith
  have hQuarticEvaluation :
      actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod
          firstFunctional.quartic =
        actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod
          secondFunctional.quartic := by
    funext jet
    exact hQuarticPointwise jet
  have hQuartic : firstFunctional.quartic = secondFunctional.quartic :=
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation_injective period hPeriod
      hQuarticEvaluation
  have hLowerEvaluation :
      actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation period hPeriod
          firstFunctional.lower =
        actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation period hPeriod
          secondFunctional.lower := by
    funext jet
    have hAtJet := congrFun hEvaluation jet
    have hQuarticAtJet := congrArg
      (fun quartic : QuarticClass period hPeriod =>
        actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod
          quartic jet) hQuartic
    dsimp [actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation] at hAtJet
    linarith
  have hLower : firstFunctional.lower = secondFunctional.lower :=
    actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation_injective period
      hPeriod hLowerEvaluation
  cases firstFunctional
  cases secondFunctional
  cases hLower
  cases hQuartic
  rfl

/-- Complete scalar coordinates of an invariant degree-four functional. -/
def actualPhysicalSecondOrderJetInvariantDegreeFourCoordinates
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod) :
    ActualPhysicalSecondOrderJetInvariantDegreeFourCoefficients period hPeriod where
  lower := actualPhysicalSecondOrderJetInvariantDegreeThreeCoordinates period hPeriod
    functional.lower
  quartic := actualPhysicalSecondOrderJetInvariantQuarticFunctionalCoordinateEquiv
    period hPeriod functional.quartic

/-- Synthesis from all scalar coefficients through degree four. -/
def actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis
    (coefficients :
      ActualPhysicalSecondOrderJetInvariantDegreeFourCoefficients period hPeriod) :
    ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod where
  lower := actualPhysicalSecondOrderJetInvariantDegreeThreeSynthesis period hPeriod
    coefficients.lower
  quartic := (actualPhysicalSecondOrderJetInvariantQuarticFunctionalCoordinateEquiv
    period hPeriod).symm coefficients.quartic

/-- Scalar-coordinate synthesis through degree four is injective. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis_injective :
    Function.Injective
      (actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis period hPeriod) := by
  intro firstCoefficients secondCoefficients hSynthesis
  apply ActualPhysicalSecondOrderJetInvariantDegreeFourCoefficients.ext
  · apply actualPhysicalSecondOrderJetInvariantDegreeThreeSynthesis_injective
      period hPeriod
    exact congrArg
      ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional.lower hSynthesis
  · apply (actualPhysicalSecondOrderJetInvariantQuarticFunctionalCoordinateEquiv
      period hPeriod).symm.injective
    exact congrArg
      ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional.quartic hSynthesis

/-- Synthesis reconstructs every invariant degree-four functional exactly. -/
@[simp]
theorem actualPhysicalSecondOrderJetInvariantDegreeFour_reconstruction
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod) :
    actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis period hPeriod
        (actualPhysicalSecondOrderJetInvariantDegreeFourCoordinates period hPeriod
          functional) = functional := by
  cases functional
  simp [actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis,
    actualPhysicalSecondOrderJetInvariantDegreeFourCoordinates]

/-- Every invariant local functional of degree at most four has one and only
one complete scalar coefficient family. -/
theorem actualPhysicalSecondOrderJetInvariantDegreeFour_existsUnique_coefficients
    (functional :
      ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod) :
    ∃! coefficients :
        ActualPhysicalSecondOrderJetInvariantDegreeFourCoefficients period hPeriod,
      actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis period hPeriod
          coefficients = functional := by
  refine ⟨actualPhysicalSecondOrderJetInvariantDegreeFourCoordinates period hPeriod
      functional, actualPhysicalSecondOrderJetInvariantDegreeFour_reconstruction
        period hPeriod functional, ?_⟩
  intro coefficients hCoefficients
  apply actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis_injective
    period hPeriod
  exact hCoefficients.trans
    (actualPhysicalSecondOrderJetInvariantDegreeFour_reconstruction
      period hPeriod functional).symm

end
end P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
end JanusFormal
