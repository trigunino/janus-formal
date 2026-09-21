import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08InvariantDeformationFreedom4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08ValuePotentialEuler4D

/-!
# T08: nonnegative scalar potentials still leave a coupling free

For any fixed scalar reference `v`, the potential `lambda * (chi - v)^2`
belongs to the actual T02 degree-at-most-four carrier and is fixed by the
installed Abelian scalar-ghost BRST. For positive lambda its scalar minimum
occurs exactly at `chi = v`, independently of lambda. This is a statement
about this local scalar potential, not a physical vacuum or a full BV action.
-/

namespace JanusFormal
namespace P0EFTJanusT08StableMassDeformation4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
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
open P0EFTJanusProgramPT06FullPhysicalScalarGhostBRSTJetComplex4D
open P0EFTJanusT08InvariantDeformationFreedom4D
open P0EFTJanusT08ValuePotentialEuler4D

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

/-- Explicit symmetric rank-one form on the existing physical jet fiber. -/
def t08LLMeasureBilinearForm : Fiber →L[Real] Fiber →L[Real] Real :=
  t08LLMeasureValue.smulRight t08LLMeasureValue

@[simp] theorem t08LLMeasureBilinearForm_apply (first second : Fiber) :
    t08LLMeasureBilinearForm first second =
      t08LLMeasureValue first * t08LLMeasureValue second := rfl

variable (period : Real) (hPeriod : period ≠ 0)

local instance : ChartedSpace ThroatCoverModel
    (MappingTorus (fixedEquatorData period hPeriod)) :=
  fixedThroatQuotientChartedSpace period hPeriod

theorem t08LLMeasureBilinearForm_invariant :
    IsActualPhysicalSecondOrderJetInvariantSymmetricBilinearForm
      period hPeriod t08LLMeasureBilinearForm := by
  constructor
  · intro first second
    change t08LLMeasureValue first * t08LLMeasureValue second =
      t08LLMeasureValue second * t08LLMeasureValue first
    exact mul_comm _ _
  · intro first second base hBase firstJet secondJet
    simp only [t08LLMeasureBilinearForm_apply,
      t08LLMeasureValue_transitionInvariant period hPeriod first second base hBase]

/-- A freely coupled centered scalar potential in the actual classified T02
carrier; all other polynomial components vanish. -/
def t08LLMeasureMassDeformation (coupling reference : Real) :
    ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod where
  lower :=
    { lower :=
        { constant := coupling * reference ^ 2
          linear := (-2 * coupling * reference) •
            ⟨t08LLMeasureValue, t08LLMeasureValue_transitionInvariant period hPeriod⟩
          quadratic := coupling •
            ⟨t08LLMeasureBilinearForm, t08LLMeasureBilinearForm_invariant period hPeriod⟩ }
      cubic := 0 }
  quartic := 0

@[simp] theorem t08LLMeasureMassDeformation_evaluation
    (coupling reference : Real) (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
      (t08LLMeasureMassDeformation period hPeriod coupling reference) jet =
        coupling * (t08LLMeasureValue jet - reference) ^ 2 := by
  simp [t08LLMeasureMassDeformation,
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
    actualPhysicalSecondOrderJetInvariantCubicEvaluation,
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation,
    t08LLMeasureBilinearForm]
  ring

/-- Even when the reference value is fixed, the coupling is not selected. -/
theorem t08LLMeasureMassDeformation_injective (reference : Real) :
    Function.Injective (fun coupling =>
      t08LLMeasureMassDeformation period hPeriod coupling reference) := by
  intro first second hEqual
  have h := congrArg (fun functional =>
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
      functional ((reference + 1) • t08LLMeasureUnitJet)) hEqual
  have hValue : t08LLMeasureValue ((reference + 1) • t08LLMeasureUnitJet) =
      reference + 1 := by
    rw [map_smul, t08LLMeasureValue_unit]
    simp
  rw [t08LLMeasureMassDeformation_evaluation,
    t08LLMeasureMassDeformation_evaluation, hValue] at h
  convert h using 1 <;> ring

/-- The same centered potential in the existing T06 spatial coordinates. -/
def t08LLMeasureSpatialMassDeformation (coupling reference : Real)
    (jet : ThroatSpatialMultiindexJet2 ValueFiber) : Real :=
  coupling * (t08LLMeasureSpatialDeformation 1 jet - reference) ^ 2

theorem t08LLMeasureSpatialMassDeformation_eq_T02
    (coupling reference : Real) (jet : ThroatSpatialMultiindexJet2 ValueFiber) :
    t08LLMeasureSpatialMassDeformation coupling reference jet =
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (t08LLMeasureMassDeformation period hPeriod coupling reference)
        (programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv jet) := by
  rw [t08LLMeasureMassDeformation_evaluation]
  change coupling * (1 * t08LLMeasureValue
      (programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv jet) - reference) ^ 2 = _
  rw [one_mul]

/-- Exact finite BRST-shift invariance for every coefficient and reference. -/
theorem t08LLMeasureSpatialMassDeformation_abelianBRST_shift
    (coupling reference amplitude : Real)
    (state : ProgramPT06FullPhysicalScalarGhostJetState4D 2) :
    t08LLMeasureSpatialMassDeformation coupling reference
        (state.1 + amplitude •
          (programPT06FullPhysicalScalarGhostJetBRST 2 state).1) =
      t08LLMeasureSpatialMassDeformation coupling reference state.1 := by
  simp only [t08LLMeasureSpatialMassDeformation,
    t08LLMeasureSpatialDeformation_abelianBRST_shift]

theorem t08LLMeasureMassDeformation_nonnegative
    {coupling : Real} (hCoupling : 0 ≤ coupling) (reference : Real) (jet : Fiber) :
    0 ≤ actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
      (t08LLMeasureMassDeformation period hPeriod coupling reference) jet := by
  rw [t08LLMeasureMassDeformation_evaluation]
  exact mul_nonneg hCoupling (sq_nonneg _)

/-- For positive coupling the scalar potential vanishes exactly at the fixed
reference; this is not a uniqueness assertion for all physical fields. -/
theorem t08LLMeasureMassDeformation_zero_iff
    {coupling : Real} (hCoupling : 0 < coupling) (reference : Real) (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
      (t08LLMeasureMassDeformation period hPeriod coupling reference) jet = 0 ↔
        t08LLMeasureValue jet = reference := by
  rw [t08LLMeasureMassDeformation_evaluation]
  simp [ne_of_gt hCoupling, sub_eq_zero]

/-- Every jet with the prescribed scalar value minimizes this scalar potential
over the model fiber, independently of the positive coupling. -/
theorem t08LLMeasureMassDeformation_minimum_iff
    {coupling : Real} (hCoupling : 0 < coupling) (reference : Real) (jet : Fiber) :
    (∀ other : Fiber,
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
          (t08LLMeasureMassDeformation period hPeriod coupling reference) jet ≤
        actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
          (t08LLMeasureMassDeformation period hPeriod coupling reference) other) ↔
      t08LLMeasureValue jet = reference := by
  constructor
  · intro hMin
    apply (t08LLMeasureMassDeformation_zero_iff period hPeriod hCoupling reference jet).mp
    apply le_antisymm
    · have h := hMin (reference • t08LLMeasureUnitJet)
      have hValue : t08LLMeasureValue (reference • t08LLMeasureUnitJet) = reference := by
        rw [map_smul, t08LLMeasureValue_unit]
        simp
      simpa only [t08LLMeasureMassDeformation_evaluation, hValue,
        sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero] using h
    · exact t08LLMeasureMassDeformation_nonnegative period hPeriod
        (le_of_lt hCoupling) reference jet
  · intro hValue other
    rw [(t08LLMeasureMassDeformation_zero_iff period hPeriod hCoupling reference jet).mpr hValue]
    exact t08LLMeasureMassDeformation_nonnegative period hPeriod
      (le_of_lt hCoupling) reference other

/-- The LL scalar coordinate on the actual value fiber, extracted through the
existing T06 jet injection rather than introducing an independent field. -/
def t08LLMeasureValueCoordinate : ValueFiber →L[Real] Real :=
  (t08LLMeasureSpatialDeformation 1).comp
    (programPT06ThroatSpatialJetCoordinateInjection programPT06SecondOrderZeroMultiIndex)

@[simp] theorem t08LLMeasureValueCoordinate_apply (value : ValueFiber) :
    t08LLMeasureValueCoordinate value = value.1.1.2.1.2 := by
  simp [t08LLMeasureValueCoordinate]

@[simp] theorem t08LLMeasureValueCoordinate_unit :
    t08LLMeasureValueCoordinate t08LLMeasureUnitVariation = 1 := by
  rw [t08LLMeasureValueCoordinate_apply]
  rfl

theorem t08LLMeasureSpatialMassDeformation_eq_valueOnly (coupling reference : Real) :
    t08LLMeasureSpatialMassDeformation coupling reference =
      valueOnly (centeredPower t08LLMeasureValueCoordinate coupling reference 2) := by
  funext jet
  simp [t08LLMeasureSpatialMassDeformation, valueOnly, centeredPower]

/-- The genuine T06 Euler expression, not just the ordinary potential slope. -/
theorem t08LLMeasureSpatialMassDeformation_euler
    (coupling reference : Real) (jet : ThroatSpatialMultiindexJet4 ValueFiber)
    (variation : ValueFiber) :
    programPT06SecondOrderLocalEuler (t08LLMeasureSpatialMassDeformation coupling reference)
      jet variation =
      2 * coupling * (t08LLMeasureValueCoordinate (jet ⟨0, by simp⟩) - reference) *
        t08LLMeasureValueCoordinate variation := by
  rw [t08LLMeasureSpatialMassDeformation_eq_valueOnly, centeredPower_euler]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- All positive coefficients have the same scalar stationary condition.
Other field coordinates remain unrestricted by this potential. -/
theorem t08LLMeasureSpatialMassDeformation_stationary_iff
    {coupling : Real} (hCoupling : 0 < coupling) (reference : Real)
    (jet : ThroatSpatialMultiindexJet4 ValueFiber) :
    programPT06SecondOrderLocalEuler
      (t08LLMeasureSpatialMassDeformation coupling reference) jet = 0 ↔
        t08LLMeasureValueCoordinate (jet ⟨0, by simp⟩) = reference := by
  constructor
  · intro hZero
    have h := congrArg (fun form => form t08LLMeasureUnitVariation) hZero
    have hProduct : (2 * coupling) *
        (t08LLMeasureValueCoordinate (jet ⟨0, by simp⟩) - reference) = 0 := by
      simpa only [t08LLMeasureSpatialMassDeformation_euler,
        t08LLMeasureValueCoordinate_unit, mul_one, _root_.zero_apply] using h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_left
      (mul_ne_zero (by norm_num) (ne_of_gt hCoupling)))
  · intro hValue
    ext variation
    rw [t08LLMeasureSpatialMassDeformation_euler, hValue]
    simp

/-- Different coefficients give different Euler expressions, despite the
common minimum and stationary condition for positive coefficients. -/
theorem t08LLMeasureSpatialMassDeformation_euler_injective (reference : Real) :
    Function.Injective (fun coupling =>
      programPT06SecondOrderLocalEuler
        (t08LLMeasureSpatialMassDeformation coupling reference)) := by
  intro first second hEqual
  let witness : ThroatSpatialMultiindexJet4 ValueFiber :=
    programPT06ThroatSpatialJetCoordinateInjection ⟨0, by simp⟩
      ((reference + 1) • t08LLMeasureUnitVariation)
  have hValue : t08LLMeasureValueCoordinate (witness ⟨0, by simp⟩) = reference + 1 := by
    change t08LLMeasureValueCoordinate
      (programPT06ThroatSpatialJetCoordinateInjection (⟨0, by simp⟩ : ThroatSpatialTruncatedIndex 4)
        ((reference + 1) • t08LLMeasureUnitVariation) ⟨0, by simp⟩) = reference + 1
    rw [programPT06ThroatSpatialJetCoordinateInjection_same,
      map_smul, t08LLMeasureValueCoordinate_unit]
    simp
  have h := congrArg (fun expression => expression witness t08LLMeasureUnitVariation) hEqual
  simp only [t08LLMeasureSpatialMassDeformation_euler,
    t08LLMeasureValueCoordinate_unit, hValue, mul_one] at h
  linarith

end
end P0EFTJanusT08StableMassDeformation4D
end JanusFormal
