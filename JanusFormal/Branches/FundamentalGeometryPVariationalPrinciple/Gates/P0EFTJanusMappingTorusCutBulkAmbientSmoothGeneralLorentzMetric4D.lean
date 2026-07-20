import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

/-!
# Smooth general Lorentz metric pulled back to the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackGlobalLorentz4D
open P0EFTJanusMappingTorusCutBulkGlobalDerivativeIsomorphism4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

private abbrev CutBulkCotangentFiber
    (point : PositiveHemisphereCutBulk period hPeriod) :=
  CutBulkTangentFiber period hPeriod point →L[Real] Real

/-- The globally certified derivative as a continuous linear equivalence. -/
def cutBulkToAmbientDerivativeEquiv
    (point : PositiveHemisphereCutBulk period hPeriod) :
    CutBulkTangentFiber period hPeriod point ≃L[Real]
      AmbientTangentFiber period hPeriod point :=
  (cutBulkToAmbient_derivative_isomorphism period hPeriod point).choose

theorem cutBulkToAmbientDerivativeEquiv_coe
    (point : PositiveHemisphereCutBulk period hPeriod) :
    (cutBulkToAmbientDerivativeEquiv period hPeriod point :
      CutBulkTangentFiber period hPeriod point →L[Real]
        AmbientTangentFiber period hPeriod point) =
      mfderiv cutCollarModelWithCorners coverModelWithCorners
        (cutBulkToAmbient period hPeriod) point :=
  (cutBulkToAmbient_derivative_isomorphism period hPeriod point).choose_spec

private def cutBulkPullbackCovectorEquiv
    (point : PositiveHemisphereCutBulk period hPeriod) :
    (AmbientTangentFiber period hPeriod point →L[Real] Real) ≃L[Real]
      CutBulkCotangentFiber period hPeriod point :=
  (cutBulkToAmbientDerivativeEquiv period hPeriod point).symm.arrowCongr
    (ContinuousLinearEquiv.refl Real Real)

/-- Musical equivalence of the pulled-back metric. -/
def cutBulkAmbientPullbackMusical
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod) :
    CutBulkTangentFiber period hPeriod point ≃L[Real]
      CutBulkCotangentFiber period hPeriod point :=
  (cutBulkToAmbientDerivativeEquiv period hPeriod point).trans
    ((metric.musical (cutBulkToAmbient period hPeriod point)).trans
      (cutBulkPullbackCovectorEquiv period hPeriod point))

@[simp]
theorem cutBulkAmbientPullbackMusical_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (first second : CutBulkTangentFiber period hPeriod point) :
    cutBulkAmbientPullbackMusical period hPeriod metric point first second =
      metric.musical (cutBulkToAmbient period hPeriod point)
        (cutBulkToAmbientDerivativeEquiv period hPeriod point first)
        (cutBulkToAmbientDerivativeEquiv period hPeriod point second) :=
  rfl

/-- Smooth Lorentz metrics on the cut bulk, with the musical inverse tied to
the same smooth covariant tensor. -/
structure CutBulkSmoothGeneralLorentzMetric where
  tensor : CutBulkSmoothSymmetricCovariantTwoTensor period hPeriod
  musical : ∀ point, CutBulkTangentFiber period hPeriod point ≃L[Real]
    CutBulkCotangentFiber period hPeriod point
  musical_eq_tensor : ∀ point,
    (musical point : CutBulkTangentFiber period hPeriod point →L[Real]
      CutBulkCotangentFiber period hPeriod point) = tensor.tensor point
  lorentzian : ∀ point, CutBulkFiberIsLorentzian period hPeriod
    (tensor.tensor point)

/-- Pullback of an ambient smooth general Lorentz metric to the cut bulk. -/
def cutBulkAmbientSmoothGeneralLorentzMetricPullback
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CutBulkSmoothGeneralLorentzMetric period hPeriod where
  tensor := cutBulkAmbientSmoothTensorPullback period hPeriod metric.tensor
  musical := cutBulkAmbientPullbackMusical period hPeriod metric
  musical_eq_tensor := by
    intro point
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    change metric.musical (cutBulkToAmbient period hPeriod point)
        (cutBulkToAmbientDerivativeEquiv period hPeriod point first)
        (cutBulkToAmbientDerivativeEquiv period hPeriod point second) =
      cutBulkAmbientTensorPullback period hPeriod
        metric.tensor.tensor.toTensorField point first second
    have hMusical :
        metric.musical (cutBulkToAmbient period hPeriod point)
            (cutBulkToAmbientDerivativeEquiv period hPeriod point first)
            (cutBulkToAmbientDerivativeEquiv period hPeriod point second) =
          metric.tensor.tensor (cutBulkToAmbient period hPeriod point)
            (cutBulkToAmbientDerivativeEquiv period hPeriod point first)
            (cutBulkToAmbientDerivativeEquiv period hPeriod point second) :=
      congrArg (fun linear =>
        linear (cutBulkToAmbientDerivativeEquiv period hPeriod point first)
          (cutBulkToAmbientDerivativeEquiv period hPeriod point second))
        (metric.musical_eq_tensor (cutBulkToAmbient period hPeriod point))
    rw [hMusical]
    rw [cutBulkAmbientTensorPullback_apply,
      ← DFunLike.congr_fun
        (cutBulkToAmbientDerivativeEquiv_coe period hPeriod point) first,
      ← DFunLike.congr_fun
        (cutBulkToAmbientDerivativeEquiv_coe period hPeriod point) second]
    rfl
  lorentzian := by
    intro point
    exact cutBulkAmbientTensorPullback_lorentzian_global period hPeriod
      metric.tensor.tensor.toTensorField metric.lorentzian point

end
end P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D
end JanusFormal
