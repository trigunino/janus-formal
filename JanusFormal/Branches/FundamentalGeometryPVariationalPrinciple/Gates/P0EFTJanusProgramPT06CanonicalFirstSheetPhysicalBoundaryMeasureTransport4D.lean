import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetRegionalPhysicalMetricStokes4D

/-!
# Physical-image measure for the canonical first-sheet boundary

The regional screen measure is pushed through the genuine mapping-torus
boundary parametrization.  The canonical adapted coordinate then transports
the affine boundary flux to this physical image, with equality of the two
integrals by `Measure.map`.

This is a measure-transport statement only.  It does not identify the
physical metric with the warped metric or assert physical nullity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFirstSheetPhysicalBoundaryMeasureTransport4D

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
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullScreenMeasureIntegratedStokes4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
open P0EFTJanusProgramPT06CanonicalFirstSheetGlobalStripCoordinate4D
open P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarRegionalStokes4D
open P0EFTJanusProgramPT06CanonicalFirstSheetRegionalPhysicalMetricStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance boundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveBulkMeasurableSpace :
    MeasurableSpace (ProgramPT06EffectiveBulk period hPeriod) := borel _

local instance effectiveBulkBorelSpace :
    BorelSpace (ProgramPT06EffectiveBulk period hPeriod) where
  measurable_eq := rfl

/-- The selected first-sheet face, mapped into the genuine effective bulk. -/
def programPT06CanonicalFirstSheetPhysicalBoundaryMap
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3) :
    ProgramPT06EffectiveBulk period hPeriod :=
  cutThroatBoundaryToBulk period hPeriod
    (programPT06CanonicalFirstSheetBoundaryMap period hPeriod pole source)

theorem programPT06CanonicalFirstSheetPhysicalBoundaryMap_continuous
    (pole : StandardEquatorialTwoSphere) :
    Continuous
      (programPT06CanonicalFirstSheetPhysicalBoundaryMap
        period hPeriod pole) := by
  exact (continuous_cutThroatBoundaryToBulk period hPeriod).comp
    (programPT06CanonicalFirstSheetBoundaryMap_contMDiff
      period hPeriod pole).continuous

theorem programPT06CanonicalFirstSheetPhysicalBoundaryMap_mem_chart
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period) :
    programPT06CanonicalFirstSheetPhysicalBoundaryMap
        period hPeriod pole source ∈
      (programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
        period hPeriod pole).source := by
  let incidence :=
    programPT06CanonicalFirstSheetFullCollarCoordinateIncidence
      period hPeriod (0 : FiniteNullFacePhysicalHilbert Unit) pole
  exact incidence.face_mem_chart source hSource

theorem programPT06CanonicalFirstSheetPhysicalBoundaryMap_coordinate
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period) :
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
        period hPeriod pole
        (programPT06CanonicalFirstSheetPhysicalBoundaryMap
          period hPeriod pole source) =
      programPT06WarpedNullHyperplaneEmbedding source := by
  let incidence :=
    programPT06CanonicalFirstSheetFullCollarCoordinateIncidence
      period hPeriod (0 : FiniteNullFacePhysicalHilbert Unit) pole
  exact incidence.face_coordinate source hSource

/-- The first-sheet physical boundary parametrization is injective on the
fundamental strip. -/
theorem programPT06CanonicalFirstSheetPhysicalBoundaryMap_injOn
    (pole : StandardEquatorialTwoSphere) :
    Set.InjOn
      (programPT06CanonicalFirstSheetPhysicalBoundaryMap
        period hPeriod pole)
      (programPT06CanonicalFirstSheetGlobalStripSourceRegion period) := by
  intro first hFirst second hSecond hEqual
  apply programPT06WarpedNullHyperplaneEmbedding_injective
  rw [← programPT06CanonicalFirstSheetPhysicalBoundaryMap_coordinate
      period hPeriod pole first hFirst,
    ← programPT06CanonicalFirstSheetPhysicalBoundaryMap_coordinate
      period hPeriod pole second hSecond,
    hEqual]

/-- Physical image of the valid canonical first-sheet boundary patch. -/
def programPT06CanonicalFirstSheetPhysicalBoundaryImage
    (pole : StandardEquatorialTwoSphere) :
    Set (ProgramPT06EffectiveBulk period hPeriod) :=
  programPT06CanonicalFirstSheetPhysicalBoundaryMap period hPeriod pole ''
    programPT06CanonicalFirstSheetGlobalStripSourceRegion period

/-- Pushforward of the regional warped screen measure to the genuine
mapping-torus boundary image. -/
def programPT06CanonicalFirstSheetPhysicalBoundaryMeasure
    (pole : StandardEquatorialTwoSphere) :
    Measure (ProgramPT06EffectiveBulk period hPeriod) :=
  Measure.map
    (programPT06CanonicalFirstSheetPhysicalBoundaryMap period hPeriod pole)
    (programPT06CanonicalFirstSheetRegionalScreenMeasure period)

theorem programPT06CanonicalFirstSheetPhysicalBoundaryMeasure_map
    (pole : StandardEquatorialTwoSphere) :
    Measure.map
        (programPT06CanonicalFirstSheetPhysicalBoundaryMap
          period hPeriod pole)
        (programPT06CanonicalFirstSheetRegionalScreenMeasure period) =
      programPT06CanonicalFirstSheetPhysicalBoundaryMeasure
        period hPeriod pole :=
  rfl

/-- Boundary flux read in the inverse adapted coordinate on the physical
chart, extended by zero outside that chart. -/
def programPT06CanonicalFirstSheetPhysicalBoundaryFlux
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    ProgramPT06EffectiveBulk period hPeriod → Real := by
  classical
  let chart :=
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole
  exact chart.source.piecewise
    (fun point =>
      programPT06WarpedNullAffineBoundaryFlux density
        (programPT06WarpedNullCollarEquiv.symm (chart point)).1)
    (fun _ => (0 : Real))

theorem programPT06CanonicalFirstSheetPhysicalBoundaryFlux_measurable
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (hDensity : Continuous density) :
    Measurable
      (programPT06CanonicalFirstSheetPhysicalBoundaryFlux
        period hPeriod pole density) := by
  classical
  let chart :=
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole
  have hSourceCoordinate : ContinuousOn
      (fun point : ProgramPT06EffectiveBulk period hPeriod =>
        (programPT06WarpedNullCollarEquiv.symm (chart point)).1)
      chart.source :=
    continuous_fst.comp_continuousOn
      (programPT06WarpedNullCollarEquiv.symm.continuous.comp_continuousOn
        chart.contMDiffOn_toFun.continuousOn)
  have hFlux : Continuous
      (programPT06WarpedNullAffineBoundaryFlux density) := by
    rw [programPT06WarpedNullAffineBoundaryFlux,
      programPT06WarpedNullCollarAffineFluxExtension_rightInverse density]
    exact hDensity
  have hOn : ContinuousOn
      (fun point : ProgramPT06EffectiveBulk period hPeriod =>
        programPT06WarpedNullAffineBoundaryFlux density
          (programPT06WarpedNullCollarEquiv.symm (chart point)).1)
      chart.source := by
    change ContinuousOn
      (programPT06WarpedNullAffineBoundaryFlux density ∘
        fun point =>
          (programPT06WarpedNullCollarEquiv.symm (chart point)).1)
      chart.source
    exact hFlux.comp_continuousOn hSourceCoordinate
  have hZero : ContinuousOn
      (fun _ : ProgramPT06EffectiveBulk period hPeriod => (0 : Real))
      chart.sourceᶜ :=
    continuous_const.continuousOn
  simpa [programPT06CanonicalFirstSheetPhysicalBoundaryFlux, chart] using
    hOn.measurable_piecewise hZero chart.open_source.measurableSet

theorem programPT06CanonicalFirstSheetPhysicalBoundaryFlux_apply
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈
      programPT06CanonicalFirstSheetGlobalStripSourceRegion period) :
    programPT06CanonicalFirstSheetPhysicalBoundaryFlux
        period hPeriod pole density
        (programPT06CanonicalFirstSheetPhysicalBoundaryMap
          period hPeriod pole source) =
      programPT06WarpedNullAffineBoundaryFlux density source := by
  classical
  have hMem := programPT06CanonicalFirstSheetPhysicalBoundaryMap_mem_chart
    period hPeriod pole source hSource
  rw [programPT06CanonicalFirstSheetPhysicalBoundaryFlux]
  simp only [Set.piecewise, hMem, if_true]
  rw [programPT06CanonicalFirstSheetPhysicalBoundaryMap_coordinate
    period hPeriod pole source hSource,
    ← programPT06WarpedNullCollar_zeroSlice source,
    programPT06WarpedNullCollarEquiv.symm_apply_apply]

/-- The pushed-forward physical integral is exactly the regional coordinate
boundary integral. -/
theorem programPT06CanonicalFirstSheetPhysicalBoundaryFlux_integral_eq
    (pole : StandardEquatorialTwoSphere)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (hDensity : Continuous density) :
    (∫ point,
        programPT06CanonicalFirstSheetPhysicalBoundaryFlux
          period hPeriod pole density point
      ∂programPT06CanonicalFirstSheetPhysicalBoundaryMeasure
        period hPeriod pole) =
      ∫ source, programPT06WarpedNullAffineBoundaryFlux density source
        ∂programPT06CanonicalFirstSheetRegionalScreenMeasure period := by
  rw [programPT06CanonicalFirstSheetPhysicalBoundaryMeasure,
    integral_map_of_stronglyMeasurable
      (programPT06CanonicalFirstSheetPhysicalBoundaryMap_continuous
        period hPeriod pole).measurable
      (programPT06CanonicalFirstSheetPhysicalBoundaryFlux_measurable
        period hPeriod pole density hDensity).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
    (programPT06CanonicalFirstSheetGlobalStripSourceRegion_isOpen
      period).measurableSet] with source hSource
  exact programPT06CanonicalFirstSheetPhysicalBoundaryFlux_apply
    period hPeriod pole density source hSource

/-- Gate 1069's regional physical-metric bulk integral equals the boundary
integral on the genuine mapping-torus image measure. -/
theorem programPT06CanonicalFirstSheetRegionalPhysicalMetric_image_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    (∫ source,
        programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
          period hPeriod pole metric density source
      ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) =
      ∫ point,
        programPT06CanonicalFirstSheetPhysicalBoundaryFlux
          period hPeriod pole density point
        ∂programPT06CanonicalFirstSheetPhysicalBoundaryMeasure
          period hPeriod pole := by
  have hDensityDifferentiable : Differentiable Real density :=
    fun source => contract.differentiable source
  rw [programPT06CanonicalFirstSheetPhysicalBoundaryFlux_integral_eq
    period hPeriod pole density hDensityDifferentiable.continuous]
  exact programPT06CanonicalFirstSheetRegionalPhysicalMetric_integrated_stokes
    period hPeriod contract pole metric

end
end P0EFTJanusProgramPT06CanonicalFirstSheetPhysicalBoundaryMeasureTransport4D
end JanusFormal
