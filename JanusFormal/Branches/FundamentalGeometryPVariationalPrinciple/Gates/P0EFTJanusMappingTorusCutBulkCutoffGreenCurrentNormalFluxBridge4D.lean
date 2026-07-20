import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCanonicalNormalFlux4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D

/-!
# Cutoff bridge to the genuine cut-bulk Green-current normal flux
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D

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
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
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
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
open P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrentCanonicalNormalFlux4D

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

/-- Genuine intrinsic Green-current flux along the canonical collar normal. -/
def canonicalCutBulkIntrinsicGreenNormalFlux
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  let point := canonicalLatitudeCutBulkCollarMap period hPeriod (base, normal)
  (intrinsicCutBulkSmoothGeneralLorentzMetric period hPeriod).musical point
    (intrinsicCutBulkSmoothScalarGreenCurrent period hPeriod field test point)
    ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm
      (canonicalLatitudeNormalVector period hPeriod base normal))

theorem canonicalCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Icc (0 : Real) 1) :
    canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test base normal =
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal := by
  exact intrinsicCutBulkSmoothScalarGreenCurrent_canonicalNormalFlux
    period hPeriod field test base normal hNormal

/-- The previously constructed global cutoff scalar current is exactly cutoff
times the normal flux of the genuine intrinsic vector current. -/
theorem cutBulkScalarCurrent_canonicalCollarPath_eq_cutoff_mul_intrinsicFlux
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Icc (0 : Real) 1) :
    cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base normal) =
      canonicalLatitudeCollarCutoff normal *
        canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test base normal := by
  rw [cutBulkScalarCurrent_canonicalCollarPath,
    Set.projIcc_of_mem zero_le_one hNormal,
    cutoffCollarScalarCurrentDensity,
    canonicalCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test base normal hNormal]

/-- In the collar interior, the existing measured divergence density is the
actual normal derivative of cutoff times the genuine intrinsic flux. -/
theorem cutoff_mul_canonicalCutBulkIntrinsicGreenNormalFlux_hasDerivAt
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    HasDerivAt
      (fun current => canonicalLatitudeCollarCutoff current *
        canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test base current)
      (cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
        field test base normal) normal := by
  have hEventually : Filter.EventuallyEq (nhds normal)
      (fun current => canonicalLatitudeCollarCutoff current *
        canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod field test base current)
      (cutoffCollarScalarCurrentDensity period hPeriod field test base) := by
    filter_upwards [isOpen_Ioo.mem_nhds hNormal] with current hCurrent
    rw [canonicalCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
      period hPeriod field test base current ⟨hCurrent.1.le, hCurrent.2.le⟩]
    rfl
  exact (cutoffCollarScalarCurrentDensity_hasDerivAt period hPeriod massSquared
    field test base normal).congr_of_eventuallyEq hEventually

end
end P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D
end JanusFormal
