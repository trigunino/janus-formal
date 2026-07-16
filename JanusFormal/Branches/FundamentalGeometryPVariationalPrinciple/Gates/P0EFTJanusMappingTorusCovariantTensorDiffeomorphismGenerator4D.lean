import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

/-! Infinitesimal diffeomorphism action on intrinsic covariant two-tensors. -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCovariantTensorDiffeomorphismGenerator4D

set_option autoImplicit false
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

/-- The genuine real curve of pullback tensor values at a fixed quotient point. -/
def tensorPullbackCurveValue
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    Real → CovariantTwoTensorFiber period hPeriod point :=
  fun t => pullbackTensorValue period hPeriod (curve t) tensor point

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

end
end P0EFTJanusMappingTorusCovariantTensorDiffeomorphismGenerator4D
end JanusFormal
