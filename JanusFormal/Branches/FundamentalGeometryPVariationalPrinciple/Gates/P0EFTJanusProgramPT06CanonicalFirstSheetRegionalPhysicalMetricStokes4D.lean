import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarRegionalStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06PhysicalCoordinateMetricDensityCorrection4D

/-!
# Regional physical-metric Stokes law in the canonical first-sheet coordinate

On the canonical finite collar, the density-corrected affine current has the
same densitized divergence for an arbitrary smooth physical Lorentz metric as
for the explicit warped metric.  Thus its coordinate fiber integral and its
regional source integral satisfy Gate 1067's Stokes law.

All integrals remain in the canonical coordinate measures.  No physical image
measure, metric isometry, null-face property, or screen-metric identification
is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFirstSheetRegionalPhysicalMetricStokes4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set MeasureTheory
open scoped Interval Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06AmbientAbsoluteVectorPullbackPiola4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullScreenMeasureIntegratedStokes4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
open P0EFTJanusProgramPT06CanonicalFirstSheetGlobalStripCoordinate4D
open P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarRegionalStokes4D
open P0EFTJanusProgramPT06PhysicalCoordinateMetricDensityCorrection4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Physical metric-volume density times divergence of the corrected affine
current, evaluated in the canonical collar coordinate. -/
def programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3)
    (radius : Real) : Real :=
  let chart :=
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole
  let coordinate := programPT06WarpedNullCollarEquiv (source, radius)
  programPT06AmbientMatrixMetricVolumeDensity
        (programPT06PhysicalCoordinateMetricMatrix
          period hPeriod chart metric) coordinate *
    programPT06AmbientMatrixMetricVolumeDivergence
      (programPT06PhysicalCoordinateMetricMatrix
        period hPeriod chart metric)
      (programPT06PhysicalCoordinateMetricDensityCorrectedCurrent
        period hPeriod chart metric
        (programPT06WarpedNullCollarAffineFluxExtension density))
      coordinate

/-- The physical corrected and warped densitized divergences agree at every
point of the valid canonical finite collar. -/
theorem programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence_eq_warped
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3)
    (radius : Real)
    (hTime : source.1 ∈ canonicalLorentzInteriorTime period)
    (hRadius : radius ∈ Set.Icc (0 : Real) 1) :
    programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
        period hPeriod pole metric density source radius =
      programPT06WarpedNullAmbientMetricVolumeDensity
          (programPT06WarpedNullCollarEquiv (source, radius)) *
        programPT06WarpedNullMetricVolumeDivergence
          (programPT06WarpedNullCollarAffineFluxExtension density)
          (programPT06WarpedNullCollarEquiv (source, radius)) := by
  let chart :=
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole
  let normal : CutCollarInterval := ⟨radius, hRadius⟩
  let coordinate := programPT06WarpedNullCollarEquiv (source, radius)
  have hCoordinate : coordinate ∈ chart.target := by
    let physicalPoint :=
      cutBulkFiniteCollarToAmbient period hPeriod
        (programPT06CanonicalFirstSheetBoundaryMap
          period hPeriod pole source, normal)
    have hPhysical : physicalPoint ∈ chart.source :=
      programPT06CanonicalFirstSheetFullCollar_mem_globalStripCoordinate
        period hPeriod pole source normal hTime
    have hChartCoordinate :
        chart physicalPoint =
          programPT06WarpedNullClosedHalfCollarEmbedding (source, normal) :=
      programPT06CanonicalFirstSheetGlobalStripCoordinate_fullCollar
        period hPeriod pole source normal hTime
    have hMap : chart physicalPoint ∈ chart.target := chart.map_source hPhysical
    change programPT06WarpedNullClosedHalfCollarEmbedding
        (source, normal) ∈ chart.target
    rw [← hChartCoordinate]
    exact hMap
  unfold programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
  dsimp only
  rw [programPT06PhysicalCoordinateMetricDensityCorrected_densitizedDivergence
    period hPeriod chart metric
      (programPT06WarpedNullCollarAffineFluxExtension density)
      coordinate hCoordinate]
  rw [programPT06AmbientMatrixMetricVolumeCurrent_warped]
  unfold programPT06WarpedNullMetricVolumeDivergence
  field_simp [programPT06WarpedNullAmbientMetricVolumeDensity_eq,
    Real.exp_ne_zero]
  rfl

/-- Fiber integral of the corrected physical metric-volume divergence in the
canonical collar coordinate. -/
def programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3) : Real :=
  ∫ radius in (0 : Real)..1,
    programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence
      period hPeriod pole metric density source radius

/-- On the valid time strip, the corrected physical fiber integral is exactly
Gate 1067's warped fiber integral. -/
theorem programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral_eq_warped
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (source : ProgramPT06NullFaceSource3)
    (hTime : source.1 ∈ canonicalLorentzInteriorTime period) :
    programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
        period hPeriod pole metric density source =
      programPT06WarpedNullMetricFiberBulkIntegral density source := by
  unfold programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
    programPT06WarpedNullMetricFiberBulkIntegral
  apply intervalIntegral.integral_congr
  intro radius hRadius
  rw [Set.uIcc_of_le zero_le_one] at hRadius
  exact
    programPT06CanonicalFirstSheetPhysicalMetricDensitizedDivergence_eq_warped
      period hPeriod pole metric density source radius hTime hRadius

/-- The corrected physical fiber bulk integrand is integrable over the
regional coordinate source measure. -/
theorem ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.physicalMetric_bulk_integrable
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Integrable
      (programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
        period hPeriod pole metric density)
      (programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) := by
  apply
    (ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.bulk_integrable
      period contract).congr
  filter_upwards [ae_restrict_mem
    (programPT06CanonicalFirstSheetGlobalStripSourceRegion_isOpen
      period).measurableSet] with source hSource
  exact
    (programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral_eq_warped
      period hPeriod pole metric density source hSource).symm

/-- Regional integration of the corrected physical bulk term equals regional
integration of the warped bulk term. -/
theorem programPT06CanonicalFirstSheetPhysicalMetricRegionalBulkIntegral_eq_warped
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    (∫ source,
        programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
          period hPeriod pole metric density source
      ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) =
      ∫ source, programPT06WarpedNullMetricFiberBulkIntegral density source
        ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
    (programPT06CanonicalFirstSheetGlobalStripSourceRegion_isOpen
      period).measurableSet] with source hSource
  exact
    programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral_eq_warped
      period hPeriod pole metric density source hSource

/-- Regional Stokes law for the density-corrected affine current in an
arbitrary smooth physical Lorentz metric, expressed in canonical coordinates. -/
theorem programPT06CanonicalFirstSheetRegionalPhysicalMetric_integrated_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    (∫ source,
        programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
          period hPeriod pole metric density source
      ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) =
      ∫ source, programPT06WarpedNullAffineBoundaryFlux density source
        ∂programPT06CanonicalFirstSheetRegionalScreenMeasure period := by
  rw [programPT06CanonicalFirstSheetPhysicalMetricRegionalBulkIntegral_eq_warped
    period hPeriod pole metric]
  exact programPT06CanonicalFirstSheetRegionalMetricVolume_integrated_stokes
    period contract

/-- Regional bundle for the corrected physical bulk and the warped boundary
flux in canonical coordinate measures. -/
theorem programPT06CanonicalFirstSheetRegionalPhysicalMetric_integrable_stokes
    {density : ProgramPT06WarpedNullHyperplaneDensity}
    (contract : ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract
      period density)
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Integrable
        (programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
          period hPeriod pole metric density)
        (programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) ∧
      Integrable (programPT06WarpedNullAffineBoundaryFlux density)
        (programPT06CanonicalFirstSheetRegionalScreenMeasure period) ∧
      (∫ source,
          programPT06CanonicalFirstSheetPhysicalMetricFiberBulkIntegral
            period hPeriod pole metric density source
        ∂programPT06CanonicalFirstSheetRegionalCoordinateSourceMeasure period) =
        ∫ source, programPT06WarpedNullAffineBoundaryFlux density source
          ∂programPT06CanonicalFirstSheetRegionalScreenMeasure period :=
  ⟨ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.physicalMetric_bulk_integrable
      period hPeriod contract pole metric,
    ProgramPT06CanonicalFirstSheetRegionalIntegratedStokesContract.boundary_integrable
      period contract,
    programPT06CanonicalFirstSheetRegionalPhysicalMetric_integrated_stokes
      period hPeriod contract pole metric⟩

end
end P0EFTJanusProgramPT06CanonicalFirstSheetRegionalPhysicalMetricStokes4D
end JanusFormal
