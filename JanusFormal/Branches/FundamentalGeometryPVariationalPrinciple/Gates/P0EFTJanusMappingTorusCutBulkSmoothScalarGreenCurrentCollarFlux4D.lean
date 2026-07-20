import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkMetricMeasureDomination4D

/-!
# Collar flux of the genuine cut-bulk Green current
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCollarFlux4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D
open P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D
open P0EFTJanusMappingTorusCutBulkIntrinsicMetricVolumeDensity4D
open P0EFTJanusMappingTorusCutBulkSmoothScalarGradient4D
open P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkMetricMeasureDomination4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

local instance cutBulkIsManifold :
    IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobal_isManifold period hPeriod

/-- A pulled-back scalar differential evaluated on the inverse derivative is
the ambient exterior derivative. -/
theorem cutBulkSmoothScalarDifferential_pullback_inverseDerivative
    (field : SmoothQuotientField period hPeriod Real)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (cutBulkToAmbient period hPeriod point)) :
    cutBulkSmoothScalarDifferential period hPeriod
        (cutBulkSmoothScalarPullback period hPeriod field) point
        ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm ambientVector) =
      mvfderiv coverModelWithCorners field.toFun
        (cutBulkToAmbient period hPeriod point) ambientVector := by
  have hPullback := DFunLike.congr_fun
    (cutBulkSmoothScalarDifferential_pullback period hPeriod field point)
    ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm ambientVector)
  apply hPullback.trans
  change mvfderiv coverModelWithCorners field.toFun
      (cutBulkToAmbient period hPeriod point)
        (mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutBulkToAmbient period hPeriod) point
          ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm ambientVector)) = _
  rw [← DFunLike.congr_fun
    (cutBulkToAmbientDerivativeEquiv_coe period hPeriod point)
    ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm ambientVector)]
  exact congrArg
    (mvfderiv coverModelWithCorners field.toFun
      (cutBulkToAmbient period hPeriod point))
    ((cutBulkToAmbientDerivativeEquiv period hPeriod point).apply_symm_apply
      ambientVector)

/-- Flux of the intrinsic pullback Green current against the inverse image of
an arbitrary ambient tangent vector. -/
theorem intrinsicCutBulkSmoothScalarGreenCurrent_flux_inverseDerivative
    (field test : SmoothQuotientField period hPeriod Real)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (cutBulkToAmbient period hPeriod point)) :
    (intrinsicCutBulkSmoothGeneralLorentzMetric period hPeriod).musical point
        (intrinsicCutBulkSmoothScalarGreenCurrent period hPeriod field test point)
        ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm ambientVector) =
      field (cutBulkToAmbient period hPeriod point) *
          mvfderiv coverModelWithCorners test.toFun
            (cutBulkToAmbient period hPeriod point) ambientVector -
        test (cutBulkToAmbient period hPeriod point) *
          mvfderiv coverModelWithCorners field.toFun
            (cutBulkToAmbient period hPeriod point) ambientVector := by
  unfold intrinsicCutBulkSmoothScalarGreenCurrent
  rw [cutBulkSmoothScalarGreenCurrent_flat]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, cutBulkSmoothScalarPullback_apply]
  rw [cutBulkSmoothScalarDifferential_pullback_inverseDerivative,
    cutBulkSmoothScalarDifferential_pullback_inverseDerivative]

end
end P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCollarFlux4D
end JanusFormal
