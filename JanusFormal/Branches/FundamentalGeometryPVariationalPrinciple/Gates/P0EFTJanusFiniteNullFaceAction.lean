import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteStratifiedBoundaryVariation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNullExpansionCountertermNonDifferentiable

/-!
# Finite null-face action and exact reparametrization law

This gate assembles one supplied one-dimensional null generator into an actual
finite action.  Its three strata are the integrated inaffinity density, the
integrated expansion counterterm and the two endpoint-joint values.

The finite normalization change is represented by

`k -> exp sigma * k`, `d lambda -> exp (-sigma) * d lambda`.

The transformed inaffinity is `exp sigma * (kappa + sigma')` and the
transformed expansion is `exp sigma * Theta`.  The two transformed face
densities differ from the original ones by the already-proved local
transgression `(A sigma)'`.  The fundamental theorem of calculus and the
oriented endpoint shifts therefore make the full action invariant, face by
face and after every finite sum.

The counterterm uses its continuous value at `Theta = 0`, where the finite
reparametrization identity still holds.  Classical variation in the expansion
variable is exposed only on the explicit nonzero-expansion domain, since the
zero extension is not differentiable at zero.

The only residual analytic input is the named interval-integrability contract.
The ambient null hypersurface, screen metric and its induced measure are not
constructed here; they must supply the one-dimensional area data and that
contract.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteNullFaceAction

set_option autoImplicit false

noncomputable section

open scoped BigOperators

open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusNullExpansionCountertermVariation
open P0EFTJanusNullExpansionCountertermNonDifferentiable
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteStratifiedBoundaryVariation

/-- Supplied reduced data for one oriented null face and its two endpoint
joints. -/
structure FiniteNullFaceActionDatum where
  generator : NullGeneratorReparametrizationData
  interval : OrientedNullInterval
  einsteinScale : ℝ
  orientationSign : ℝ
  orientationSignAdmissible : IsOrientationSign orientationSign
  renormalizationLengthScale : ℝ
  renormalizationLengthScalePositive : 0 < renormalizationLengthScale
  initialJointAction : ℝ
  finalJointAction : ℝ

/-- Common coefficient multiplying the two face densities and their joint
transgression. -/
def nullFaceCoefficient (face : FiniteNullFaceActionDatum) : ℝ :=
  face.einsteinScale * face.orientationSign

/-- Inaffinity contribution to the original face density. -/
def inaffinityFaceDensity
    (face : FiniteNullFaceActionDatum) (parameter : ℝ) : ℝ :=
  nullFaceCoefficient face * face.generator.area parameter *
    face.generator.inaffinity parameter

/-- Expansion counterterm contribution, with its continuous value at zero. -/
def expansionCountertermFaceDensity
    (face : FiniteNullFaceActionDatum) (parameter : ℝ) : ℝ :=
  nullFaceCoefficient face * face.generator.area parameter *
    zeroExtendedExpansionCountertermFactor
      face.renormalizationLengthScale
      (face.generator.expansion parameter)

/-- Sum of the two original face densities. -/
def nullFaceDensity
    (face : FiniteNullFaceActionDatum) (parameter : ℝ) : ℝ :=
  inaffinityFaceDensity face parameter +
    expansionCountertermFaceDensity face parameter

/-- The integrated inaffinity action. -/
def integratedInaffinityAction (face : FiniteNullFaceActionDatum) : ℝ :=
  ∫ parameter in face.interval.initialParameter..face.interval.finalParameter,
    inaffinityFaceDensity face parameter

/-- The integrated expansion-counterterm action. -/
def integratedExpansionCountertermAction
    (face : FiniteNullFaceActionDatum) : ℝ :=
  ∫ parameter in face.interval.initialParameter..face.interval.finalParameter,
    expansionCountertermFaceDensity face parameter

/-- The supplied action values on the two endpoint joints. -/
def endpointJointAction (face : FiniteNullFaceActionDatum) : ℝ :=
  face.initialJointAction + face.finalJointAction

/-- Actual interval integral of the combined null-face density. -/
def integratedNullFaceAction (face : FiniteNullFaceActionDatum) : ℝ :=
  ∫ parameter in face.interval.initialParameter..face.interval.finalParameter,
    nullFaceDensity face parameter

/-- Full action of one finite null face and its endpoints. -/
def finiteNullFaceAction (face : FiniteNullFaceActionDatum) : ℝ :=
  integratedNullFaceAction face + endpointJointAction face

/-- The sole analytic contract left to the ambient geometric realization. -/
structure NullFaceIntervalIntegrability
    (face : FiniteNullFaceActionDatum) : Prop where
  inaffinity :
    IntervalIntegrable (inaffinityFaceDensity face) MeasureTheory.volume
      face.interval.initialParameter face.interval.finalParameter
  expansionCounterterm :
    IntervalIntegrable (expansionCountertermFaceDensity face)
      MeasureTheory.volume face.interval.initialParameter
      face.interval.finalParameter
  reparametrizationShift :
    IntervalIntegrable (localFaceShift face.generator) MeasureTheory.volume
      face.interval.initialParameter face.interval.finalParameter

/-- Under a finite generator rescaling the parameter measure acquires the
inverse exponential weight. -/
def reparametrizedInaffinityFaceDensity
    (face : FiniteNullFaceActionDatum) (parameter : ℝ) : ℝ :=
  nullFaceCoefficient face * face.generator.area parameter *
    Real.exp (-face.generator.sigma parameter) *
      (Real.exp (face.generator.sigma parameter) *
        shiftedInaffinity face.generator parameter)

/-- The expansion counterterm after the same finite rescaling. -/
def reparametrizedExpansionCountertermFaceDensity
    (face : FiniteNullFaceActionDatum) (parameter : ℝ) : ℝ :=
  nullFaceCoefficient face * face.generator.area parameter *
    Real.exp (-face.generator.sigma parameter) *
      zeroExtendedExpansionCountertermFactor
        face.renormalizationLengthScale
        (Real.exp (face.generator.sigma parameter) *
          face.generator.expansion parameter)

/-- Combined transformed face density. -/
def reparametrizedNullFaceDensity
    (face : FiniteNullFaceActionDatum) (parameter : ℝ) : ℝ :=
  reparametrizedInaffinityFaceDensity face parameter +
    reparametrizedExpansionCountertermFaceDensity face parameter

/-- The transformed endpoint values carry the opposite oriented primitive. -/
def reparametrizedEndpointJointAction
    (face : FiniteNullFaceActionDatum) : ℝ :=
  (face.initialJointAction +
      nullFaceCoefficient face *
        endpointPrimitive face.generator face.interval.initialParameter) +
    (face.finalJointAction -
      nullFaceCoefficient face *
        endpointPrimitive face.generator face.interval.finalParameter)

/-- Integrated transformed face density. -/
def integratedReparametrizedNullFaceAction
    (face : FiniteNullFaceActionDatum) : ℝ :=
  ∫ parameter in face.interval.initialParameter..face.interval.finalParameter,
    reparametrizedNullFaceDensity face parameter

/-- Full transformed face-plus-joints action. -/
def reparametrizedFiniteNullFaceAction
    (face : FiniteNullFaceActionDatum) : ℝ :=
  integratedReparametrizedNullFaceAction face +
    reparametrizedEndpointJointAction face

/-- Finite scaling law for the continuously extended expansion counterterm.
It remains true at zero even though classical differentiability fails there. -/
theorem zeroExtendedExpansionCountertermFactor_reparametrized
    (lengthScale sigma expansion : ℝ) (hLength : 0 < lengthScale) :
    Real.exp (-sigma) *
        zeroExtendedExpansionCountertermFactor lengthScale
          (Real.exp sigma * expansion) =
      zeroExtendedExpansionCountertermFactor lengthScale expansion +
        expansion * sigma := by
  rw [zeroExtendedExpansionCountertermFactor_eq]
  by_cases hExpansion : expansion = 0
  · simp [hExpansion, expansionCountertermFactor]
  · have hScaled : Real.exp sigma * expansion ≠ 0 :=
      mul_ne_zero (Real.exp_ne_zero sigma) hExpansion
    have hLengthNe : lengthScale ≠ 0 := hLength.ne'
    have hArgument : lengthScale * |expansion| ≠ 0 :=
      mul_ne_zero hLengthNe (abs_ne_zero.mpr hExpansion)
    rw [expansionCountertermFactor, expansionCountertermFactor]
    rw [abs_mul, abs_of_pos (Real.exp_pos sigma)]
    have hLog :
        Real.log (lengthScale * (Real.exp sigma * |expansion|)) =
          Real.log (lengthScale * |expansion|) + sigma := by
      have hProduct :
          lengthScale * (Real.exp sigma * |expansion|) =
            (lengthScale * |expansion|) * Real.exp sigma := by ring
      rw [hProduct]
      rw [Real.log_mul hArgument (Real.exp_ne_zero sigma), Real.log_exp]
    rw [hLog]
    have hExp : Real.exp (-sigma) * Real.exp sigma = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      Real.exp (-sigma) *
          (Real.exp sigma * expansion *
            (Real.log (lengthScale * |expansion|) + sigma)) =
        (Real.exp (-sigma) * Real.exp sigma) * expansion *
          (Real.log (lengthScale * |expansion|) + sigma) := by ring
      _ = expansion * Real.log (lengthScale * |expansion|) +
          expansion * sigma := by rw [hExp]; ring

/-- The transformed inaffinity density is the original density plus the
inaffinity part of the local transgression. -/
theorem reparametrizedInaffinityFaceDensity_eq
    (face : FiniteNullFaceActionDatum) (parameter : ℝ) :
    reparametrizedInaffinityFaceDensity face parameter =
      inaffinityFaceDensity face parameter +
        nullFaceCoefficient face *
          inaffinityDensityShift face.generator parameter := by
  have hExp :
      Real.exp (-face.generator.sigma parameter) *
          Real.exp (face.generator.sigma parameter) = 1 := by
    rw [← Real.exp_add]
    simp
  simp only [reparametrizedInaffinityFaceDensity,
    inaffinityFaceDensity, inaffinityDensityShift_eq]
  calc
    nullFaceCoefficient face * face.generator.area parameter *
          Real.exp (-face.generator.sigma parameter) *
          (Real.exp (face.generator.sigma parameter) *
            shiftedInaffinity face.generator parameter) =
        nullFaceCoefficient face * face.generator.area parameter *
          (Real.exp (-face.generator.sigma parameter) *
            Real.exp (face.generator.sigma parameter)) *
          shiftedInaffinity face.generator parameter := by ring
    _ = nullFaceCoefficient face * face.generator.area parameter *
          shiftedInaffinity face.generator parameter := by rw [hExp]; ring
    _ = nullFaceCoefficient face * face.generator.area parameter *
          face.generator.inaffinity parameter +
        nullFaceCoefficient face *
          (face.generator.area parameter *
            face.generator.sigmaDerivative parameter) := by
      simp [shiftedInaffinity]
      ring

/-- The transformed expansion counterterm is the original counterterm plus
the expansion part of the local transgression. -/
theorem reparametrizedExpansionCountertermFaceDensity_eq
    (face : FiniteNullFaceActionDatum) (parameter : ℝ) :
    reparametrizedExpansionCountertermFaceDensity face parameter =
      expansionCountertermFaceDensity face parameter +
        nullFaceCoefficient face *
          expansionDensityShift face.generator parameter := by
  rw [reparametrizedExpansionCountertermFaceDensity,
    expansionCountertermFaceDensity]
  calc
    nullFaceCoefficient face * face.generator.area parameter *
          Real.exp (-face.generator.sigma parameter) *
          zeroExtendedExpansionCountertermFactor
            face.renormalizationLengthScale
            (Real.exp (face.generator.sigma parameter) *
              face.generator.expansion parameter) =
        nullFaceCoefficient face * face.generator.area parameter *
          (Real.exp (-face.generator.sigma parameter) *
            zeroExtendedExpansionCountertermFactor
              face.renormalizationLengthScale
              (Real.exp (face.generator.sigma parameter) *
                face.generator.expansion parameter)) := by ring
    _ = nullFaceCoefficient face * face.generator.area parameter *
          (zeroExtendedExpansionCountertermFactor
              face.renormalizationLengthScale
              (face.generator.expansion parameter) +
            face.generator.expansion parameter *
              face.generator.sigma parameter) := by
      rw [zeroExtendedExpansionCountertermFactor_reparametrized
        face.renormalizationLengthScale
        (face.generator.sigma parameter)
        (face.generator.expansion parameter)
        face.renormalizationLengthScalePositive]
    _ = nullFaceCoefficient face * face.generator.area parameter *
          zeroExtendedExpansionCountertermFactor
            face.renormalizationLengthScale
            (face.generator.expansion parameter) +
        nullFaceCoefficient face *
          expansionDensityShift face.generator parameter := by
      simp only [expansionDensityShift]
      ring

/-- Exact pointwise finite reparametrization law for the complete face
density. -/
theorem reparametrizedNullFaceDensity_eq
    (face : FiniteNullFaceActionDatum) (parameter : ℝ) :
    reparametrizedNullFaceDensity face parameter =
      nullFaceDensity face parameter +
        nullFaceCoefficient face * localFaceShift face.generator parameter := by
  rw [reparametrizedNullFaceDensity, nullFaceDensity,
    reparametrizedInaffinityFaceDensity_eq,
    reparametrizedExpansionCountertermFaceDensity_eq]
  simp only [localFaceShift]
  ring

/-- The combined face integral is exactly the sum of the inaffinity and
expansion-counterterm contributions. -/
theorem integratedNullFaceAction_eq_three_strata
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    finiteNullFaceAction face =
      integratedInaffinityAction face +
        integratedExpansionCountertermAction face +
          endpointJointAction face := by
  rw [finiteNullFaceAction, integratedNullFaceAction]
  simp_rw [nullFaceDensity]
  rw [intervalIntegral.integral_add contract.inaffinity
    contract.expansionCounterterm]
  rfl

/-- Existing FTOC datum extracted from the single integrability contract. -/
def reparametrizationVariationDatum
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) : NullFaceDatum where
  generator := face.generator
  interval := face.interval
  faceShiftIntervalIntegrable := contract.reparametrizationShift

/-- The transformed integrated face differs by the oriented endpoint
primitive. -/
theorem integratedReparametrizedNullFaceAction_eq
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    integratedReparametrizedNullFaceAction face =
      integratedNullFaceAction face +
        nullFaceCoefficient face *
          (endpointPrimitive face.generator face.interval.finalParameter -
            endpointPrimitive face.generator face.interval.initialParameter) := by
  have hBase :
      IntervalIntegrable (nullFaceDensity face) MeasureTheory.volume
        face.interval.initialParameter face.interval.finalParameter :=
    contract.inaffinity.add contract.expansionCounterterm
  have hShift :
      IntervalIntegrable
        (fun parameter =>
          nullFaceCoefficient face * localFaceShift face.generator parameter)
        MeasureTheory.volume face.interval.initialParameter
        face.interval.finalParameter :=
    contract.reparametrizationShift.const_mul _
  rw [integratedReparametrizedNullFaceAction]
  have hPointwise :
      reparametrizedNullFaceDensity face =
        fun parameter =>
          nullFaceDensity face parameter +
            nullFaceCoefficient face * localFaceShift face.generator parameter := by
    funext parameter
    exact reparametrizedNullFaceDensity_eq face parameter
  rw [hPointwise]
  rw [intervalIntegral.integral_add hBase hShift]
  rw [intervalIntegral.integral_const_mul]
  rw [integratedNullFaceAction]
  have hFTOC := integratedNullFaceShift_eq_endpointTransgression
    (reparametrizationVariationDatum face contract)
  change
    (∫ parameter in
        face.interval.initialParameter..face.interval.finalParameter,
      localFaceShift face.generator parameter) =
      endpointPrimitive face.generator face.interval.finalParameter -
        endpointPrimitive face.generator face.interval.initialParameter at hFTOC
  rw [hFTOC]

/-- The endpoint-joint action shifts by the negative face transgression. -/
theorem reparametrizedEndpointJointAction_eq
    (face : FiniteNullFaceActionDatum) :
    reparametrizedEndpointJointAction face =
      endpointJointAction face -
        nullFaceCoefficient face *
          (endpointPrimitive face.generator face.interval.finalParameter -
            endpointPrimitive face.generator face.interval.initialParameter) := by
  simp only [reparametrizedEndpointJointAction, endpointJointAction]
  ring

/-- Exact finite reparametrization invariance of one null face with its two
endpoint joints. -/
theorem reparametrizedFiniteNullFaceAction_eq
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    reparametrizedFiniteNullFaceAction face = finiteNullFaceAction face := by
  rw [reparametrizedFiniteNullFaceAction, finiteNullFaceAction,
    integratedReparametrizedNullFaceAction_eq face contract,
    reparametrizedEndpointJointAction_eq]
  ring

/-- Parameter values on the oriented interval where the classical expansion
variation is admissible. -/
def classicalExpansionVariationParameterDomain
    (face : FiniteNullFaceActionDatum) : Set ℝ :=
  Set.uIcc face.interval.initialParameter face.interval.finalParameter ∩
    {parameter |
      face.generator.expansion parameter ∈ admissibleNonzeroExpansionDomain}

theorem mem_classicalExpansionVariationParameterDomain_iff
    (face : FiniteNullFaceActionDatum) (parameter : ℝ) :
    parameter ∈ classicalExpansionVariationParameterDomain face ↔
      parameter ∈
          Set.uIcc face.interval.initialParameter face.interval.finalParameter ∧
        face.generator.expansion parameter ≠ 0 := by
  simp [classicalExpansionVariationParameterDomain,
    mem_admissibleNonzeroExpansionDomain_iff]

/-- On the explicit face domain the counterterm has its exact classical
derivative in the expansion variable. -/
theorem expansionCounterterm_hasDerivAt_on_classicalDomain
    (face : FiniteNullFaceActionDatum) (parameter : ℝ)
    (hParameter :
      parameter ∈ classicalExpansionVariationParameterDomain face) :
    HasDerivAt
      (zeroExtendedExpansionCountertermFactor
        face.renormalizationLengthScale)
      (expansionCountertermDerivativeCoefficient
        face.renormalizationLengthScale
        (face.generator.expansion parameter))
      (face.generator.expansion parameter) := by
  rw [zeroExtendedExpansionCountertermFactor_eq]
  exact expansionCountertermFactor_hasDerivAt_on_admissibleDomain
    face.renormalizationLengthScale
    (face.generator.expansion parameter)
    face.renormalizationLengthScalePositive hParameter.2

/-- At zero expansion the action value is still admissible and continuous. -/
theorem expansionCounterterm_continuousAt_zero
    (face : FiniteNullFaceActionDatum) :
    ContinuousAt
      (zeroExtendedExpansionCountertermFactor
        face.renormalizationLengthScale) 0 :=
  zeroExtendedExpansionCountertermFactor_continuousAt_zero
    face.renormalizationLengthScale
    face.renormalizationLengthScalePositive

/-- But zero cannot be silently included in the classical variation domain. -/
theorem expansionCounterterm_not_differentiableAt_zero
    (face : FiniteNullFaceActionDatum) :
    ¬ DifferentiableAt ℝ
      (zeroExtendedExpansionCountertermFactor
        face.renormalizationLengthScale) 0 :=
  zeroExtendedExpansionCountertermFactor_not_differentiableAt_zero
    face.renormalizationLengthScale
    face.renormalizationLengthScalePositive

/-- Total action for any finite collection of null faces and endpoints. -/
def totalFiniteNullBoundaryAction
    {Face : Type*} [Fintype Face]
    (faces : Face → FiniteNullFaceActionDatum) : ℝ :=
  ∑ face : Face, finiteNullFaceAction (faces face)

/-- Total transformed action for the same finite collection. -/
def totalReparametrizedFiniteNullBoundaryAction
    {Face : Type*} [Fintype Face]
    (faces : Face → FiniteNullFaceActionDatum) : ℝ :=
  ∑ face : Face, reparametrizedFiniteNullFaceAction (faces face)

/-- Exact reparametrization invariance survives every finite stratification. -/
theorem totalReparametrizedFiniteNullBoundaryAction_eq
    {Face : Type*} [Fintype Face]
    (faces : Face → FiniteNullFaceActionDatum)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    totalReparametrizedFiniteNullBoundaryAction faces =
      totalFiniteNullBoundaryAction faces := by
  apply Finset.sum_congr rfl
  intro face _
  exact reparametrizedFiniteNullFaceAction_eq (faces face) (contracts face)

end

end P0EFTJanusFiniteNullFaceAction
end JanusFormal
