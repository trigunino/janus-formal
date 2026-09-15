import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetGlobalStripCoordinate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCoordinateIncidence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCompactSupportedStokes4D

/-!
# Regional Stokes law on the canonical first-sheet finite collar

The global-strip coordinate contains the whole finite normal interval over the
open fundamental time strip.  This gate packages that full-collar incidence
and restricts the already proved warped-null integrated Stokes law to densities
supported inside the strip.

The selected stereographic pole and the temporal gluing seam remain excluded.
No physical image measure or physical metric-volume transport is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarRegionalStokes4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullScreenMeasureIntegratedStokes4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06WarpedNullCompactSupportedStokes4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
open P0EFTJanusProgramPT06WarpedNullCoordinateIncidence4D
open P0EFTJanusProgramPT06CanonicalFirstSheetGlobalStripCoordinate4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Gate 1064 incidence strengthened by chart validity and the exact adapted
coordinate on the whole finite collar. -/
structure ProgramPT06WarpedNullFullCollarCoordinateIncidenceDatum
    (input : FiniteNullFacePhysicalHilbert Unit)
    extends ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input where
  collar_mem_chart : ∀ parameter : ProgramPT06WarpedNullClosedHalfCollar,
    parameter.1 ∈ sourceDomain →
      cutBulkFiniteCollarToAmbient period hPeriod
          (boundaryMap parameter.1, parameter.2) ∈ coordinateChart.source
  collar_coordinate : ∀ parameter : ProgramPT06WarpedNullClosedHalfCollar,
    parameter.1 ∈ sourceDomain →
      coordinateChart
          (cutBulkFiniteCollarToAmbient period hPeriod
            (boundaryMap parameter.1, parameter.2)) =
        programPT06WarpedNullClosedHalfCollarEmbedding parameter

/-- Source points whose time lies strictly inside one fundamental period. -/
def programPT06CanonicalFirstSheetGlobalStripSourceRegion :
    Set ProgramPT06NullFaceSource3 :=
  {source | source.1 ∈ canonicalLorentzInteriorTime period}

theorem programPT06CanonicalFirstSheetGlobalStripSourceRegion_isOpen :
    IsOpen (programPT06CanonicalFirstSheetGlobalStripSourceRegion period) := by
  unfold programPT06CanonicalFirstSheetGlobalStripSourceRegion
    canonicalLorentzInteriorTime
  exact isOpen_Ioo.preimage continuous_fst

theorem programPT06CanonicalFirstSheetGlobalStripSourceRegion_nonempty
    (hPeriod : period ≠ 0) :
    (programPT06CanonicalFirstSheetGlobalStripSourceRegion period).Nonempty := by
  let midpoint : Real := (min 0 period + max 0 period) / 2
  have hEndpoints : min 0 period < max 0 period :=
    min_lt_max.mpr (Ne.symm hPeriod)
  refine ⟨(midpoint, 0), ?_⟩
  change midpoint ∈ Set.Ioo (min 0 period) (max 0 period)
  constructor <;> dsimp [midpoint] <;> linarith

private theorem programPT06CutBulkFiniteCollarToAmbient_zeroFace
    (boundary : CutThroatBoundary period hPeriod) :
    cutBulkFiniteCollarToAmbient period hPeriod
        (boundary, (⊥ : CutCollarInterval)) =
      cutThroatBoundaryToBulk period hPeriod boundary := by
  unfold cutBulkFiniteCollarToAmbient
  change cutBulkToAmbient period hPeriod
      (cutCollarAttachment period hPeriod
        (cutThroatFace period hPeriod boundary)) = _
  rw [cutCollarAttachment_cutThroatFace,
    cutBulkToAmbient_cutBoundaryInclusion]

/-- The global-strip coordinate supplies an inhabited full-collar incidence
over the interior-time first-sheet region. -/
def programPT06CanonicalFirstSheetFullCollarCoordinateIncidence
    (input : FiniteNullFacePhysicalHilbert Unit)
    (pole : StandardEquatorialTwoSphere) :
    ProgramPT06WarpedNullFullCollarCoordinateIncidenceDatum
      period hPeriod input where
  input_mem_domain := by
    change input ∈ (Set.univ : Set (FiniteNullFacePhysicalHilbert Unit))
    exact Set.mem_univ input
  sourceDomain := programPT06CanonicalFirstSheetGlobalStripSourceRegion period
  sourceDomain_isOpen :=
    programPT06CanonicalFirstSheetGlobalStripSourceRegion_isOpen period
  sourceDomain_nonempty :=
    programPT06CanonicalFirstSheetGlobalStripSourceRegion_nonempty period hPeriod
  boundaryMap := programPT06CanonicalFirstSheetBoundaryMap
    period hPeriod pole
  boundaryMap_contMDiffOn :=
    programPT06CanonicalFirstSheetBoundaryMap_contMDiffOn_three
      period hPeriod pole
      (programPT06CanonicalFirstSheetGlobalStripSourceRegion period)
  coordinateChart :=
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole
  face_mem_chart := by
    intro source hSource
    rw [← programPT06CutBulkFiniteCollarToAmbient_zeroFace
      period hPeriod
      (programPT06CanonicalFirstSheetBoundaryMap period hPeriod pole source)]
    exact programPT06CanonicalFirstSheetFullCollar_mem_globalStripCoordinate
      period hPeriod pole source (⊥ : CutCollarInterval) hSource
  face_coordinate := by
    intro source hSource
    rw [← programPT06CutBulkFiniteCollarToAmbient_zeroFace
      period hPeriod
      (programPT06CanonicalFirstSheetBoundaryMap period hPeriod pole source)]
    rw [programPT06CanonicalFirstSheetGlobalStripCoordinate_fullCollar
      period hPeriod pole source (⊥ : CutCollarInterval) hSource]
    change programPT06WarpedNullClosedHalfCollarEmbedding
        (programPT06WarpedNullZeroFace source) = _
    rw [programPT06WarpedNullClosedHalfCollarEmbedding_zeroFace]
  collar_mem_chart := by
    intro parameter hSource
    exact programPT06CanonicalFirstSheetFullCollar_mem_globalStripCoordinate
      period hPeriod pole parameter.1 parameter.2 hSource
  collar_coordinate := by
    intro parameter hSource
    exact programPT06CanonicalFirstSheetGlobalStripCoordinate_fullCollar
      period hPeriod pole parameter.1 parameter.2 hSource

/-- Coordinate source measure restricted to the valid fundamental strip. -/
def programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure :
    Measure ProgramPT06NullFaceSource3 :=
  programPT06WarpedNullCoordinateSourceMeasure.restrict
    (programPT06CanonicalFirstSheetGlobalStripSourceRegion period)

/-- Warped screen measure restricted to the same strip. -/
def programPT06CanonicalFirstSheetRegionalScreenMeasure :
    Measure ProgramPT06NullFaceSource3 :=
  programPT06WarpedNullScreenMeasure.restrict
    (programPT06CanonicalFirstSheetGlobalStripSourceRegion period)

/-- The existing global analytic contract, together with support wholly inside
the valid physical coordinate strip. -/
structure ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
    (density : ProgramPT06WarpedNullHyperplaneDensity) : Prop
    extends ProgramPT06WarpedNullIntegratedStokesContract density where
  tsupport_subset_region :
    tsupport density ⊆
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period

/-- Differentiability and compact support inside the strip imply the regional
contract. -/
theorem programPT06CanonicalFirstSheetRegionalIntegratedStokesContract_of_compactSupport
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (hDensity : Differentiable Real density)
    (hCompact : HasCompactSupport density)
    (hSupport : tsupport density ⊆
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period) :
    ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density where
  toProgramPT06WarpedNullIntegratedStokesContract :=
    programPT06WarpedNullIntegratedStokesContract_of_compactSupport
      hDensity hCompact
  tsupport_subset_region := hSupport

private theorem ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.density_eq_zero
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∉
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period) :
    density source = 0 := by
  exact image_eq_zero_of_notMem_tsupport fun hSupport =>
    hSource (contract.tsupport_subset_region hSupport)

private theorem ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.bulk_eq_zero
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∉
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period) :
    programPT06WarpedNullMetricFiberBulkIntegral density source = 0 := by
  rw [programPT06WarpedNullMetricFiberBulkIntegral_eq_weightedDensity source
    (contract.differentiable source)]
  simp [programPT06WarpedNullScreenWeightedDensity,
    ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.density_eq_zero
      period contract source hSource]

private theorem ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.boundary_eq_zero
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∉
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period) :
    programPT06WarpedNullAffineBoundaryFlux density source = 0 := by
  rw [programPT06WarpedNullAffineBoundaryFlux,
    programPT06WarpedNullCollarAffineFluxExtension_rightInverse]
  exact
    ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.density_eq_zero
      period contract source hSource

theorem ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.bulk_integrable
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density) :
    Integrable (programPT06WarpedNullMetricFiberBulkIntegral density)
      (programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) := by
  exact contract.toProgramPT06WarpedNullIntegratedStokesContract.bulk_integrable
    |>.mono_measure Measure.restrict_le_self

theorem ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.boundary_integrable
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density) :
    Integrable (programPT06WarpedNullAffineBoundaryFlux density)
      (programPT06CanonicalFirstSheetRegionalScreenMeasure period) := by
  exact contract.toProgramPT06WarpedNullIntegratedStokesContract.boundary_integrable
    |>.mono_measure Measure.restrict_le_self

theorem ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.bulk_integral_eq_global
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density) :
    (∫ source, programPT06WarpedNullMetricFiberBulkIntegral density source
      ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) =
      ∫ source, programPT06WarpedNullMetricFiberBulkIntegral density source
        ∂programPT06WarpedNullCoordinateSourceMeasure := by
  change (∫ source in
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period,
      programPT06WarpedNullMetricFiberBulkIntegral density source
      ∂programPT06WarpedNullCoordinateSourceMeasure) = _
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun source hSource =>
    ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.bulk_eq_zero
      period contract source hSource

theorem ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.boundary_integral_eq_global
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density) :
    (∫ source, programPT06WarpedNullAffineBoundaryFlux density source
      ∂programPT06CanonicalFirstSheetRegionalScreenMeasure period) =
      ∫ source, programPT06WarpedNullAffineBoundaryFlux density source
        ∂programPT06WarpedNullScreenMeasure := by
  change (∫ source in
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period,
      programPT06WarpedNullAffineBoundaryFlux density source
      ∂programPT06WarpedNullScreenMeasure) = _
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun source hSource =>
    ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.boundary_eq_zero
      period contract source hSource

/-- The integrated warped-null Stokes identity restricted to the canonical
physical coordinate strip. -/
theorem programPT06CanonicalFirstSheetRegionalMetricVolume_integrated_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density) :
    (∫ source, programPT06WarpedNullMetricFiberBulkIntegral density source
      ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) =
      ∫ source, programPT06WarpedNullAffineBoundaryFlux density source
        ∂programPT06CanonicalFirstSheetRegionalScreenMeasure period := by
  rw [ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.bulk_integral_eq_global
      period contract,
    ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.boundary_integral_eq_global
      period contract]
  exact programPT06WarpedNullMetricVolume_integrated_stokes
    contract.toProgramPT06WarpedNullIntegratedStokesContract

/-- Regional bundle: both restricted integrals exist and satisfy Stokes. -/
theorem programPT06CanonicalFirstSheetRegionalMetricVolume_integrable_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density) :
    Integrable (programPT06WarpedNullMetricFiberBulkIntegral density)
        (programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) ∧
      Integrable (programPT06WarpedNullAffineBoundaryFlux density)
        (programPT06CanonicalFirstSheetRegionalScreenMeasure period) ∧
      (∫ source, programPT06WarpedNullMetricFiberBulkIntegral density source
        ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) =
        ∫ source, programPT06WarpedNullAffineBoundaryFlux density source
          ∂programPT06CanonicalFirstSheetRegionalScreenMeasure period :=
  ⟨ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.bulk_integrable
      period contract,
    ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.boundary_integrable
      period contract,
    programPT06CanonicalFirstSheetRegionalMetricVolume_integrated_stokes
      period contract⟩

end
end P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarRegionalStokes4D
end JanusFormal
