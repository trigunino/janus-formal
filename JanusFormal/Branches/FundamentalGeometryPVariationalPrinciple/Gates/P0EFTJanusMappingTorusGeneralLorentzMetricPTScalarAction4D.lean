import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D

/-!
# PT pullback of a general Lorentz metric and its scalar density

This gate transports the musical equivalence together with the already smooth
PT pullback of the covariant tensor.  It then specializes the general frame
naturality theorem to the analytic PT diffeomorphism.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D

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

/-- The genuine tangent equivalence of the analytic PT diffeomorphism. -/
def analyticPTDerivative
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      TangentFiber period hPeriod (reflectedSpherePT period hPeriod point) :=
  diffeomorphismDerivative period hPeriod
    (reflectedSpherePTDiffeomorph period hPeriod) point

@[simp]
theorem analyticPTDerivative_apply
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    analyticPTDerivative period hPeriod point vector =
      mfderiv coverModelWithCorners coverModelWithCorners
        (reflectedSpherePT period hPeriod) point vector := by
  unfold analyticPTDerivative diffeomorphismDerivative
  rfl

/-- PT pullback of a general Lorentz metric, including the musical
equivalence tied to the pulled covariant tensor. -/
def smoothGeneralLorentzMetricPTPullback
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothGeneralLorentzMetric period hPeriod where
  tensor :=
    P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D.smoothPTTensorPullback
      period hPeriod metric.tensor
  musical := fun point =>
    pullbackMusical period hPeriod (analyticPTDerivative period hPeriod point)
      (metric.musical (reflectedSpherePT period hPeriod point))
  musical_eq_tensor := by
    intro point
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    change metric.musical (reflectedSpherePT period hPeriod point)
        (analyticPTDerivative period hPeriod point first)
        (analyticPTDerivative period hPeriod point second) =
      metric.tensor.tensor (reflectedSpherePT period hPeriod point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point second)
    rw [analyticPTDerivative_apply, analyticPTDerivative_apply]
    exact DFunLike.congr_fun
      (DFunLike.congr_fun
        (metric.musical_eq_tensor (reflectedSpherePT period hPeriod point)) _)
      _
  lorentzian :=
    P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D.smoothPTTensorPullback_lorentzian
      period hPeriod
      (P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D.analyticPTTensorPullbackLocalSmoothness
        period hPeriod)
      metric.tensor metric.lorentzian

/-- A general metric is determined by its covariant tensor because its
musical equivalence is required to coerce to that same tensor. -/
theorem smoothGeneralLorentzMetric_ext
    {first second : SmoothGeneralLorentzMetric period hPeriod}
    (hTensor : first.tensor = second.tensor) : first = second := by
  cases first with
  | mk firstTensor firstMusical firstEq firstLorentzian =>
    cases second with
    | mk secondTensor secondMusical secondEq secondLorentzian =>
      dsimp at hTensor
      subst secondTensor
      have hMusical : firstMusical = secondMusical := by
        funext point
        apply ContinuousLinearEquiv.ext
        funext vector
        have hFirst := congrArg (fun current => current vector) (firstEq point)
        have hSecond := congrArg (fun current => current vector) (secondEq point)
        exact hFirst.trans hSecond.symm
      subst secondMusical
      rfl

@[simp]
theorem smoothGeneralLorentzMetricPTPullback_tensor_involutive
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    (smoothGeneralLorentzMetricPTPullback period hPeriod
      (smoothGeneralLorentzMetricPTPullback period hPeriod metric)).tensor =
        metric.tensor :=
  P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D.smoothPTTensorPullback_involutive
    period hPeriod metric.tensor

@[simp]
theorem smoothGeneralLorentzMetricPTPullback_involutive
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    smoothGeneralLorentzMetricPTPullback period hPeriod
      (smoothGeneralLorentzMetricPTPullback period hPeriod metric) = metric := by
  apply smoothGeneralLorentzMetric_ext period hPeriod
  exact smoothGeneralLorentzMetricPTPullback_tensor_involutive
    period hPeriod metric

/-- PT plus sector exchange on two general Lorentz metrics. -/
def smoothGeneralLorentzMetricPTExchange
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) :
    SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod :=
  (smoothGeneralLorentzMetricPTPullback period hPeriod metrics.2,
    smoothGeneralLorentzMetricPTPullback period hPeriod metrics.1)

@[simp]
theorem smoothGeneralLorentzMetricPTExchange_involutive
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) :
    smoothGeneralLorentzMetricPTExchange period hPeriod
      (smoothGeneralLorentzMetricPTExchange period hPeriod metrics) = metrics := by
  simp [smoothGeneralLorentzMetricPTExchange]

/-- The intrinsic scalar density is exactly natural under analytic PT when
the metric, scalar and tangent frame are pulled back coherently. -/
theorem holonomicScalarDensity_pt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) :
    holonomicScalarDensity period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
        massSquared
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) field)
        point frame =
      holonomicScalarDensity period hPeriod metric massSquared field
        (reflectedSpherePT period hPeriod point)
        (fun index => analyticPTDerivative period hPeriod point (frame index)) := by
  rw [holonomicScalarDensity_eq_fiber]
  exact holonomicScalarDensity_diffeomorphism period hPeriod
    (reflectedSpherePTDiffeomorph period hPeriod) metric massSquared field
      point frame

end

end P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
end JanusFormal
