import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D

/-!
# PT naturality of the general-metric throat trace

The differential of the throat inclusion intertwines intrinsic and ambient
PT.  Consequently restriction of an ambient PT-pulled metric is exactly the
intrinsic PT pullback of its restricted covariant tensor.  The statement is
also packaged for the two-sector PT/exchange action.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTNaturality4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev ThroatTangentFiber
    (point : EffectiveThroat period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

/-- Intrinsic differential of the actual throat PT involution. -/
def throatPTDerivative
    (point : EffectiveThroat period hPeriod) :
    ThroatTangentFiber period hPeriod point →L[Real]
      ThroatTangentFiber period hPeriod
        (fixedThroatPT period hPeriod point) :=
  mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
    (fixedThroatPT period hPeriod) point

@[simp]
theorem throatPTDerivative_apply
    (point : EffectiveThroat period hPeriod)
    (vector : ThroatTangentFiber period hPeriod point) :
    throatPTDerivative period hPeriod point vector =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (fixedThroatPT period hPeriod) point vector :=
  rfl

/-- Differentiated equivariance of the actual throat inclusion. -/
theorem fixedThroatQuotientInclusion_mfderiv_pt_equivariant
    (point : EffectiveThroat period hPeriod)
    (vector : ThroatTangentFiber period hPeriod point) :
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod)
        (fixedThroatPT period hPeriod point)
        (throatPTDerivative period hPeriod point vector) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (reflectedSpherePT period hPeriod)
        (fixedThroatQuotientInclusion period hPeriod point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point vector) := by
  have hThroat :=
    (fixedThroatPT_contMDiff period hPeriod).mdifferentiableAt
      (x := point) (by simp)
  have hInclusion :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).mdifferentiableAt
      (x := fixedThroatPT period hPeriod point) (by simp)
  have hAmbient :=
    (reflectedSpherePT_contMDiff period hPeriod).mdifferentiableAt
      (x := fixedThroatQuotientInclusion period hPeriod point) (by simp)
  have hInclusionAt :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).mdifferentiableAt
      (x := point) (by simp)
  have hLeft := mfderiv_comp_apply point hInclusion hThroat vector
  have hRight := mfderiv_comp_apply point hAmbient hInclusionAt vector
  have hFunctions :
      fixedThroatQuotientInclusion period hPeriod ∘
          fixedThroatPT period hPeriod =
        reflectedSpherePT period hPeriod ∘
          fixedThroatQuotientInclusion period hPeriod := by
    funext current
    exact fixedThroatQuotientInclusion_pt_equivariant
      period hPeriod current
  rw [hFunctions] at hLeft
  exact hLeft.symm.trans hRight

/-- Pointwise intrinsic PT pullback of a smooth throat tensor. -/
def throatPTTensorPullbackValue
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorFiber period hPeriod point :=
  let derivative := throatPTDerivative period hPeriod point
  (derivative.precomp Real).comp
    ((tensor.tensor (fixedThroatPT period hPeriod point)).comp derivative)

@[simp]
theorem throatPTTensorPullbackValue_apply
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    throatPTTensorPullbackValue period hPeriod tensor point first second =
      tensor.tensor (fixedThroatPT period hPeriod point)
        (throatPTDerivative period hPeriod point first)
        (throatPTDerivative period hPeriod point second) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction commutes pointwise with analytic PT pullback. -/
theorem generalLorentzMetricThroatTrace_pt_natural
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    (generalLorentzMetricThroatTrace period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric)).tensor
        point first second =
      throatPTTensorPullbackValue period hPeriod
        (generalLorentzMetricThroatTrace period hPeriod metric)
        point first second := by
  simp only [generalLorentzMetricThroatTrace_apply,
    throatPTTensorPullbackValue_apply]
  change
    metric.tensor.tensor
        (reflectedSpherePT period hPeriod
          (fixedThroatQuotientInclusion period hPeriod point))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod)
          (fixedThroatQuotientInclusion period hPeriod point)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod) point first))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod)
          (fixedThroatQuotientInclusion period hPeriod point)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod) point second)) = _
  rw [fixedThroatQuotientInclusion_mfderiv_pt_equivariant
      period hPeriod point first,
    fixedThroatQuotientInclusion_mfderiv_pt_equivariant
      period hPeriod point second,
    fixedThroatQuotientInclusion_pt_equivariant period hPeriod point]

/-- The two-sector metric trace obeys PT together with sector exchange. -/
theorem generalLorentzMetricThroatTrace_ptExchange_natural
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    ((generalLorentzMetricThroatTrace period hPeriod
          (smoothGeneralLorentzMetricPTExchange period hPeriod metrics).1).tensor
          point first second =
        throatPTTensorPullbackValue period hPeriod
          (generalLorentzMetricThroatTrace period hPeriod metrics.2)
          point first second) ∧
      ((generalLorentzMetricThroatTrace period hPeriod
          (smoothGeneralLorentzMetricPTExchange period hPeriod metrics).2).tensor
          point first second =
        throatPTTensorPullbackValue period hPeriod
          (generalLorentzMetricThroatTrace period hPeriod metrics.1)
          point first second) := by
  constructor
  · simpa only [smoothGeneralLorentzMetricPTExchange] using
      generalLorentzMetricThroatTrace_pt_natural
        period hPeriod metrics.2 point first second
  · simpa only [smoothGeneralLorentzMetricPTExchange] using
      generalLorentzMetricThroatTrace_pt_natural
        period hPeriod metrics.1 point first second

end

end P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTNaturality4D
end JanusFormal
