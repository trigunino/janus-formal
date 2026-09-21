import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06FullPhysicalScalarGhostBRSTJetComplex4D

/-!
# T08: an unselected coupling on the existing physical jet carrier

The genuine LL-measure scalar value defines an invariant linear member of
T02's degree-at-most-four class. Its arbitrary real coefficient survives the
existing scalar-ghost Abelian gauge-slot BRST, and its T06 Euler expression
detects that coefficient. Thus these particular constraints leave a genuine
non-Euler-null coupling free. No nonlinear diffeomorphism or full BV
invariance of this deformation is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusT08InvariantDeformationFreedom4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeTwoFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantCubicFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeThreeFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06FullPhysicalGaugeGradientBRSTJetComplex4D
open P0EFTJanusProgramPT06FullPhysicalScalarGhostBRSTJetComplex4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

local instance : NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D.actualLLNormedAddCommGroup
local instance : NormedSpace Real ActualLLSecondOrderJetFiber :=
  P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D.actualLLNormedSpace
local instance : FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional

attribute [local instance]
  actualPhysicalValueProductNormedAddCommGroup
  actualPhysicalValueProductNormedSpace
  actualPhysicalValueProductFinsuppSecondJetFiniteDimensional

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber
private abbrev ValueFiber := ActualPhysicalValueProductFiber

/-- The actual LL-measure value, a field coordinate rather than a constant
local density. -/
def t08LLMeasureValue : Fiber →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun jet => jet.1.1.2.1.2.value
      map_add' := by intro first second; rfl
      map_smul' := by intro scalar jet; rfl }

@[simp] theorem t08LLMeasureValue_apply (jet : Fiber) :
    t08LLMeasureValue jet = jet.1.1.2.1.2.value := rfl

variable (period : Real) (hPeriod : period ≠ 0)

local instance : ChartedSpace ThroatCoverModel
    (MappingTorus (fixedEquatorData period hPeriod)) :=
  fixedThroatQuotientChartedSpace period hPeriod

/-- Genuine atlas transitions preserve this globally trivial scalar value. -/
theorem t08LLMeasureValue_transitionInvariant :
    IsActualPhysicalSecondOrderJetTransitionInvariant period hPeriod
      t08LLMeasureValue := by
  intro first second base _ jet
  change (actualThroatConstantFiberSecondOrderJetCoordChange period hPeriod
    first.ll.1.2 second.ll.1.2 base jet.1.1.2.1.2).value =
      jet.1.1.2.1.2.value
  unfold actualThroatConstantFiberSecondOrderJetCoordChange
  split <;> simp [FramedSecondOrderJetConstantFiberBaseChange.toContinuousLinearMap_apply]

/-- An explicit real family inside the already classified T02 carrier. -/
def t08LLMeasureInvariantDeformation (coupling : Real) :
    ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod where
  lower :=
    { lower :=
        { constant := 0
          linear := coupling •
            ⟨t08LLMeasureValue, t08LLMeasureValue_transitionInvariant period hPeriod⟩
          quadratic := 0 }
      cubic := 0 }
  quartic := 0

@[simp] theorem t08LLMeasureInvariantDeformation_evaluation
    (coupling : Real) (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
      (t08LLMeasureInvariantDeformation period hPeriod coupling) jet =
        coupling * t08LLMeasureValue jet := by
  simp [t08LLMeasureInvariantDeformation,
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
    actualPhysicalSecondOrderJetInvariantCubicEvaluation,
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation]

/-- A concrete test jet supported only in the LL-measure value. -/
def t08LLMeasureUnitJet : Fiber :=
  (((0, ((0, ⟨1, 0, 0, fun _ _ => rfl⟩), 0)), 0), 0)

@[simp] theorem t08LLMeasureValue_unit :
    t08LLMeasureValue t08LLMeasureUnitJet = 1 := rfl

theorem t08LLMeasureInvariantDeformation_injective :
    Function.Injective (t08LLMeasureInvariantDeformation period hPeriod) := by
  intro first second hEqual
  have h := congrArg (fun functional =>
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
      functional t08LLMeasureUnitJet) hEqual
  simpa only [t08LLMeasureInvariantDeformation_evaluation,
    t08LLMeasureValue_unit, mul_one] using h

/-- The same deformation in T06's genuine spatial second-jet coordinates. -/
def t08LLMeasureSpatialDeformation (coupling : Real) :
    ThroatSpatialMultiindexJet2 ValueFiber →L[Real] Real :=
  coupling • t08LLMeasureValue.comp
    programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem t08LLMeasureSpatialDeformation_apply
    (coupling : Real) (jet : ThroatSpatialMultiindexJet2 ValueFiber) :
    t08LLMeasureSpatialDeformation coupling jet =
      coupling * (jet programPT06SecondOrderZeroMultiIndex).1.1.2.1.2 := rfl

/-- This is exactly the T02 deformation, transported by the existing bridge. -/
theorem t08LLMeasureSpatialDeformation_eq_T02
    (coupling : Real) (jet : ThroatSpatialMultiindexJet2 ValueFiber) :
    t08LLMeasureSpatialDeformation coupling jet =
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (t08LLMeasureInvariantDeformation period hPeriod coupling)
        (programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv jet) := by
  rw [t08LLMeasureInvariantDeformation_evaluation]
  rfl

/-- The installed scalar-ghost BRST changes only gauge slots in the physical
component, so its variation of the LL-measure deformation vanishes. -/
theorem t08LLMeasureSpatialDeformation_abelianBRST_zero
    (coupling : Real) (state : ProgramPT06FullPhysicalScalarGhostJetState4D 2) :
    t08LLMeasureSpatialDeformation coupling
      (programPT06FullPhysicalScalarGhostJetBRST 2 state).1 = 0 := by
  rw [t08LLMeasureSpatialDeformation_apply]
  change coupling * (0 : Real) = 0
  exact mul_zero coupling

/-- Exact finite-shift invariance also holds, with arbitrary scalar amplitude. -/
theorem t08LLMeasureSpatialDeformation_abelianBRST_shift
    (coupling amplitude : Real)
    (state : ProgramPT06FullPhysicalScalarGhostJetState4D 2) :
    t08LLMeasureSpatialDeformation coupling
        (state.1 + amplitude •
          (programPT06FullPhysicalScalarGhostJetBRST 2 state).1) =
      t08LLMeasureSpatialDeformation coupling state.1 := by
  simp only [map_add, map_smul,
    t08LLMeasureSpatialDeformation_abelianBRST_zero, smul_zero, add_zero]

/-- The actual field variation supported in the LL-measure value. -/
def t08LLMeasureUnitVariation : ValueFiber :=
  (((0, ((0, 1), 0)), 0), 0)

/-- The existing T06 Euler operator detects the free coefficient. Thus this
family is not merely a family of different representatives with zero Euler
expression. -/
theorem t08LLMeasureSpatialDeformation_euler
    (coupling : Real) (jet : ThroatSpatialMultiindexJet4 ValueFiber) :
    programPT06SecondOrderLocalEuler (t08LLMeasureSpatialDeformation coupling)
      jet t08LLMeasureUnitVariation = coupling := by
  rw [programPT06SecondOrderLocalEuler_linear]
  simp [t08LLMeasureSpatialDeformation_apply,
    programPT06ThroatSpatialJetCoordinateInjection, t08LLMeasureUnitVariation]

theorem t08LLMeasureSpatialDeformation_euler_nonzero
    {coupling : Real} (hCoupling : coupling ≠ 0)
    (jet : ThroatSpatialMultiindexJet4 ValueFiber) :
    programPT06SecondOrderLocalEuler
      (t08LLMeasureSpatialDeformation coupling) jet ≠ 0 := by
  intro hZero
  have h := congrArg (fun functional => functional t08LLMeasureUnitVariation) hZero
  rw [t08LLMeasureSpatialDeformation_euler] at h
  exact hCoupling h

/-- Even agreement of Euler expressions forces agreement of these couplings. -/
theorem t08LLMeasureSpatialDeformation_euler_injective
    (first second : Real)
    (jet : ThroatSpatialMultiindexJet4 ValueFiber)
    (hEqual : programPT06SecondOrderLocalEuler
        (t08LLMeasureSpatialDeformation first) jet =
      programPT06SecondOrderLocalEuler
        (t08LLMeasureSpatialDeformation second) jet) : first = second := by
  have h := congrArg (fun functional => functional t08LLMeasureUnitVariation) hEqual
  simpa only [t08LLMeasureSpatialDeformation_euler] using h

end
end P0EFTJanusT08InvariantDeformationFreedom4D
end JanusFormal
