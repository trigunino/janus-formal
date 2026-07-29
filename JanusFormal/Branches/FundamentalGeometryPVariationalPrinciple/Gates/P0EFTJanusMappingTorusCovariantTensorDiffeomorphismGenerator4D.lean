import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

/-! Infinitesimal diffeomorphism action on intrinsic covariant two-tensors. -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCovariantTensorDiffeomorphismGenerator4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CovariantTwoTensorFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real]
    (TangentFiber period hPeriod point →L[Real] Real)

private instance covariantTwoTensorFiberNormedAddCommGroup
    (point : EffectiveQuotient period hPeriod) :
    NormedAddCommGroup
      (CovariantTwoTensorFiber period hPeriod point) :=
  inferInstanceAs (NormedAddCommGroup
    (CoverCoordinates →L[Real] (CoverCoordinates →L[Real] Real)))

private instance covariantTwoTensorFiberNormedSpace
    (point : EffectiveQuotient period hPeriod) :
    NormedSpace Real (CovariantTwoTensorFiber period hPeriod point) :=
  inferInstanceAs (NormedSpace Real
    (CoverCoordinates →L[Real] (CoverCoordinates →L[Real] Real)))

/-- The genuine real curve of pullback tensor values at a fixed quotient point. -/
def tensorPullbackCurveValue
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    Real → CovariantTwoTensorFiber period hPeriod point :=
  fun t => pullbackTensorValue period hPeriod (curve t) tensor point

/-- Pullback tensor curves are additive in the tensor slot. -/
theorem tensorPullbackCurveValue_add
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (first second : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    tensorPullbackCurveValue period hPeriod curve (first + second) point =
      tensorPullbackCurveValue period hPeriod curve first point +
        tensorPullbackCurveValue period hPeriod curve second point := by
  funext parameter
  apply ContinuousLinearMap.ext
  intro left
  apply ContinuousLinearMap.ext
  intro right
  rfl

/-- Pullback tensor curves are homogeneous in the tensor slot. -/
theorem tensorPullbackCurveValue_smul
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (coefficient : Real)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    tensorPullbackCurveValue period hPeriod curve
        (coefficient • tensor) point =
      coefficient •
        tensorPullbackCurveValue period hPeriod curve tensor point := by
  funext parameter
  apply ContinuousLinearMap.ext
  intro left
  apply ContinuousLinearMap.ext
  intro right
  rfl

/-- Infinitesimal pullback action, retaining the full tensor-valued derivative. -/
def covariantTensorDiffeomorphismGeneratorAt
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    CovariantTwoTensorFiber period hPeriod point :=
  deriv (tensorPullbackCurveValue period hPeriod curve tensor point) 0

@[simp] theorem tensorPullbackCurveValue_apply
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (t : Real) (first second : TangentFiber period hPeriod point) :
    tensorPullbackCurveValue period hPeriod curve tensor point t first second =
      tensor (curve t point)
        (mfderiv coverModelWithCorners coverModelWithCorners (curve t) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners (curve t) point second) := by
  exact pullbackTensorValue_apply period hPeriod (curve t) tensor point first second

theorem covariantTensorDiffeomorphismGeneratorAt_eq_of_hasFDerivAt
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (derivative : Real →L[Real] CovariantTwoTensorFiber period hPeriod point)
    (hDerivative : HasFDerivAt
      (tensorPullbackCurveValue period hPeriod curve tensor point) derivative 0) :
    covariantTensorDiffeomorphismGeneratorAt period hPeriod curve tensor point =
      derivative 1 := by
  simp [covariantTensorDiffeomorphismGeneratorAt, deriv, hDerivative.fderiv]

/-- Evaluation of the generator supplied by a Fréchet derivative.  The
underlying curve is the intrinsic pullback formula above, so both tangent
arguments continue to carry the manifold derivative of the diffeomorphism. -/
theorem covariantTensorDiffeomorphismGeneratorAt_apply_of_hasFDerivAt
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (derivative : Real →L[Real] CovariantTwoTensorFiber period hPeriod point)
    (hDerivative : HasFDerivAt
      (tensorPullbackCurveValue period hPeriod curve tensor point) derivative 0)
    (first second : TangentFiber period hPeriod point) :
    covariantTensorDiffeomorphismGeneratorAt period hPeriod curve tensor point
        first second =
      derivative 1 first second := by
  rw [covariantTensorDiffeomorphismGeneratorAt_eq_of_hasFDerivAt
    period hPeriod curve tensor point derivative hDerivative]

/-- The infinitesimal tensor generator is additive whenever both pullback
orbits are differentiable at the identity. -/
theorem covariantTensorDiffeomorphismGeneratorAt_add
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (first second : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hFirst : DifferentiableAt Real
      (tensorPullbackCurveValue period hPeriod curve first point) 0)
    (hSecond : DifferentiableAt Real
      (tensorPullbackCurveValue period hPeriod curve second point) 0) :
    covariantTensorDiffeomorphismGeneratorAt period hPeriod curve
        (first + second) point =
      covariantTensorDiffeomorphismGeneratorAt period hPeriod curve first point +
        covariantTensorDiffeomorphismGeneratorAt
          period hPeriod curve second point := by
  simpa only [covariantTensorDiffeomorphismGeneratorAt,
    tensorPullbackCurveValue_add] using
      (deriv_add (𝕜 := Real) hFirst hSecond)

/-- The infinitesimal tensor generator is unconditionally homogeneous in
the tensor slot. -/
theorem covariantTensorDiffeomorphismGeneratorAt_smul
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (coefficient : Real)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    covariantTensorDiffeomorphismGeneratorAt period hPeriod curve
        (coefficient • tensor) point =
      coefficient •
        covariantTensorDiffeomorphismGeneratorAt
          period hPeriod curve tensor point := by
  simpa only [covariantTensorDiffeomorphismGeneratorAt,
    tensorPullbackCurveValue_smul] using
      (deriv_const_smul_field (𝕜 := Real) coefficient
        (tensorPullbackCurveValue period hPeriod curve tensor point)
        (x := 0))

/-- Exact regularity needed to bundle one tensor pullback curve as an action
linear in the tensor field. -/
structure TensorPullbackCurveDifferentiability
    (curve : Real → SpacetimeDiffeomorphism period hPeriod) : Prop where
  differentiableAt :
    ∀ (tensor : SmoothCovariantTwoTensor period hPeriod) point,
      DifferentiableAt Real
        (tensorPullbackCurveValue period hPeriod curve
          tensor.toTensorField point) 0

/-- For one differentiable diffeomorphism curve, the fiber generator is a
genuine linear map in the tensor field. -/
def covariantTensorDiffeomorphismGeneratorLinearAt
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (regularity :
      TensorPullbackCurveDifferentiability period hPeriod curve)
    (point : EffectiveQuotient period hPeriod) :
    SmoothCovariantTwoTensor period hPeriod →ₗ[Real]
      CovariantTwoTensorFiber period hPeriod point where
  toFun := fun tensor =>
    covariantTensorDiffeomorphismGeneratorAt
      period hPeriod curve tensor.toTensorField point
  map_add' := fun first second => by
    have hAdd :
        (first + second).toTensorField =
          first.toTensorField + second.toTensorField := by
      funext current
      rfl
    rw [hAdd]
    exact covariantTensorDiffeomorphismGeneratorAt_add
      period hPeriod curve first.toTensorField second.toTensorField point
      (regularity.differentiableAt first point)
      (regularity.differentiableAt second point)
  map_smul' := fun coefficient tensor => by
    have hSmul :
        (coefficient • tensor).toTensorField =
          coefficient • tensor.toTensorField := by
      funext current
      rfl
    rw [hSmul]
    exact covariantTensorDiffeomorphismGeneratorAt_smul
      period hPeriod curve coefficient tensor.toTensorField point

end
end P0EFTJanusMappingTorusCovariantTensorDiffeomorphismGenerator4D
end JanusFormal
