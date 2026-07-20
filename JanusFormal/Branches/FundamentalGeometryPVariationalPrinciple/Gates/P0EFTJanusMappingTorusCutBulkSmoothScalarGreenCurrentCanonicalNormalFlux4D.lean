import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCollarFlux4D

/-!
# Canonical normal flux of the genuine cut-bulk Green current
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCanonicalNormalFlux4D

set_option autoImplicit false
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
open P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkMetricMeasureDomination4D
open P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCollarFlux4D

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

/-- On the canonical collar, the normal flux of the genuine intrinsic current
is exactly the established scalar Green--Wronskian current. -/
theorem intrinsicCutBulkSmoothScalarGreenCurrent_canonicalNormalFlux
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Icc (0 : Real) 1) :
    let point := canonicalLatitudeCutBulkCollarMap period hPeriod (base, normal)
    (intrinsicCutBulkSmoothGeneralLorentzMetric period hPeriod).musical point
        (intrinsicCutBulkSmoothScalarGreenCurrent period hPeriod field test point)
        ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm
          (canonicalLatitudeNormalVector period hPeriod base normal)) =
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal := by
  dsimp only
  rw [intrinsicCutBulkSmoothScalarGreenCurrent_flux_inverseDerivative]
  rw [cutBulkToAmbient_canonicalLatitudeCutBulkCollarMap period hPeriod
    (base, normal) hNormal]
  change canonicalLatitudeValue period hPeriod field base normal *
        mvfderiv coverModelWithCorners test.toFun
          (quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod base) normal)
          (canonicalLatitudeNormalVector period hPeriod base normal) -
      canonicalLatitudeValue period hPeriod test base normal *
        mvfderiv coverModelWithCorners field.toFun
          (quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod base) normal)
          (canonicalLatitudeNormalVector period hPeriod base normal) = _
  rw [← canonicalLatitudeDerivative_eq_mvfderiv_normal,
    ← canonicalLatitudeDerivative_eq_mvfderiv_normal]
  exact (canonicalLatitudeScalarGreenCurrent_eq_normalNoetherPairing
    period hPeriod field test base normal).symm

end
end P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCanonicalNormalFlux4D
end JanusFormal
