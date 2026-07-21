import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D

/-!
# Canonical cut-bulk collar measure versus intrinsic Lorentz volume
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkMetricMeasureDomination4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentCollarCoordinateBridge4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkToAmbientGlobalSmooth4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D
open P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

local instance quotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance quotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance bulkMeasurableSpace :
    MeasurableSpace (PositiveHemisphereCutBulk period hPeriod) := borel _

local instance bulkBorelSpace :
    BorelSpace (PositiveHemisphereCutBulk period hPeriod) where
  measurable_eq := rfl

/-- The cut-bulk collar map followed by the natural ambient map is exactly
the previously used quotient collar map. -/
theorem cutBulkToAmbient_canonicalLatitudeCutBulkCollarMap
    (parameter : CanonicalLatitudeCollarParameter)
    (hNormal : parameter.2 ∈ Set.Icc (0 : Real) 1) :
    cutBulkToAmbient period hPeriod
        (canonicalLatitudeCutBulkCollarMap period hPeriod parameter) =
      canonicalLatitudeCollarMap period hPeriod parameter := by
  rcases parameter with ⟨base, normal⟩
  simp only at hNormal ⊢
  simp [canonicalLatitudeCutBulkCollarMap,
    canonicalLatitudeCutBulkCollarPath,
    canonicalLatitudeCutBulkCollarLift, cutCollarAttachment,
    canonicalLatitudeCutBoundaryFirstLift, canonicalLatitudeCollarMap,
    canonicalLatitudeAnchor, quotientNormalLatitude, normalLatitudeCover,
    cutBulkToAmbient,
    cutBulkCoverToAmbient, cutCollarCoverAttachment, positiveLatitudeFiber,
    Set.projIcc_of_mem _ hNormal]

/-- Pushing the canonical cut-bulk collar measure to the ambient quotient
recovers the established latitude-collar pushforward exactly. -/
theorem map_cutBulkCanonicalCollarMeasure_toAmbient :
    Measure.map (cutBulkToAmbient period hPeriod)
        (cutBulkCanonicalCollarMeasure period hPeriod) =
      Measure.map (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeCollarMeasure period) := by
  rw [cutBulkCanonicalCollarMeasure, Measure.map_map
    (cutBulkToAmbient_contMDiff period hPeriod).continuous.measurable
    (continuous_canonicalLatitudeCutBulkCollarMap period hPeriod).measurable]
  apply Measure.map_congr
  rw [canonicalLatitudeCollarMeasure]
  change ∀ᵐ parameter ∂(canonicalLatitudeBaseMeasure period).prod
      canonicalLatitudeUnitNormalMeasure,
    cutBulkToAmbient period hPeriod
        (canonicalLatitudeCutBulkCollarMap period hPeriod parameter) =
      canonicalLatitudeCollarMap period hPeriod parameter
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_eq
      ((cutBulkToAmbient_contMDiff period hPeriod).continuous.comp
        (continuous_canonicalLatitudeCutBulkCollarMap period hPeriod))
      (canonicalLatitudeCollarMap_continuous period hPeriod)).measurableSet).2
  filter_upwards [] with base
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with normal hNormal
  exact cutBulkToAmbient_canonicalLatitudeCutBulkCollarMap period hPeriod
    (base, normal) ⟨le_of_lt hNormal.1, hNormal.2⟩

/-- The transported cut-bulk collar measure is controlled by the canonical
intrinsic Lorentz volume with the already proved sharp coarea constant. -/
theorem map_cutBulkCanonicalCollarMeasure_le_intrinsicLorentzVolume :
    Measure.map (cutBulkToAmbient period hPeriod)
        (cutBulkCanonicalCollarMeasure period hPeriod) ≤
      canonicalLatitudeCoareaMeasureConstant •
        intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [map_cutBulkCanonicalCollarMeasure_toAmbient period hPeriod]
  exact canonicalLatitudeMeasureToSphereCoareaDomination_of_positiveLatitude
    period hPeriod canonicalPositiveLatitudeMeasureDomination_radialPolar

end
end P0EFTJanusMappingTorusCutBulkMetricMeasureDomination4D
end JanusFormal
