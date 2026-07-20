import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryGlobalHomeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryScalarCurrentIntegralCancellation4D

/-! # Canonical measure on the global cut-bulk boundary -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalBoundaryMeasure4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentIntegralCancellation4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBoundaryGlobalHomeomorph4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance boundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

local instance boundaryMeasurableSpace :
    MeasurableSpace (CutThroatBoundary period hPeriod) := borel _

local instance boundaryBorelSpace :
    BorelSpace (CutThroatBoundary period hPeriod) where
  measurable_eq := rfl

/-- The intrinsic boundary subtype of the global cut bulk. -/
abbrev CutBulkGlobalBoundary :=
  letI := cutBulkGlobalChartedSpace period hPeriod
  ↥(cutCollarModelWithCorners.boundary
    (PositiveHemisphereCutBulk period hPeriod))

local instance globalBoundaryMeasurableSpace :
    MeasurableSpace (CutBulkGlobalBoundary period hPeriod) := borel _

local instance globalBoundaryBorelSpace :
    BorelSpace (CutBulkGlobalBoundary period hPeriod) where
  measurable_eq := rfl

/-- Pushforward of the canonical positive double-throat measure to the exact
global manifold boundary. -/
def cutBulkGlobalBoundaryCanonicalMeasure :
    Measure (CutBulkGlobalBoundary period hPeriod) := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact Measure.map (cutBoundaryGlobalBoundaryHomeomorph period hPeriod)
    (cutBoundaryCanonicalMeasure period hPeriod)

theorem integral_cutBulkGlobalBoundaryCanonicalMeasure
    (function : CutBulkGlobalBoundary period hPeriod → Real)
    (hFunction : Continuous function) :
    ∫ boundary, function boundary
        ∂cutBulkGlobalBoundaryCanonicalMeasure period hPeriod =
      ∫ throat, function
        (cutBoundaryGlobalBoundaryHomeomorph period hPeriod throat)
        ∂cutBoundaryCanonicalMeasure period hPeriod := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  rw [cutBulkGlobalBoundaryCanonicalMeasure]
  exact integral_map
    (cutBoundaryGlobalBoundaryHomeomorph period hPeriod).continuous.measurable.aemeasurable
    hFunction.aestronglyMeasurable

/-- The descended scalar current, read on the exact global boundary subtype. -/
def cutBulkGlobalBoundaryScalarCurrent
    (field test : SmoothQuotientField period hPeriod Real) :
    CutBulkGlobalBoundary period hPeriod → Real := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact fun boundary => cutBoundaryScalarCurrent period hPeriod field test
    ((cutBoundaryGlobalBoundaryHomeomorph period hPeriod).symm boundary)

theorem continuous_cutBulkGlobalBoundaryScalarCurrent
    (field test : SmoothQuotientField period hPeriod Real) :
    Continuous (cutBulkGlobalBoundaryScalarCurrent period hPeriod field test) := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact (cutBoundaryScalarCurrent_contMDiff period hPeriod field test).continuous.comp
    (cutBoundaryGlobalBoundaryHomeomorph period hPeriod).symm.continuous

/-- The already-proved unoriented cancellation transports to the exact global
boundary. This is not the oriented Stokes flux formula. -/
theorem integral_cutBulkGlobalBoundaryScalarCurrent_eq_zero
    (field test : SmoothQuotientField period hPeriod Real) :
    ∫ boundary, cutBulkGlobalBoundaryScalarCurrent period hPeriod field test boundary
        ∂cutBulkGlobalBoundaryCanonicalMeasure period hPeriod = 0 := by
  rw [integral_cutBulkGlobalBoundaryCanonicalMeasure period hPeriod _
    (continuous_cutBulkGlobalBoundaryScalarCurrent period hPeriod field test)]
  simpa [cutBulkGlobalBoundaryScalarCurrent] using
    integral_cutBoundaryScalarCurrent_eq_zero period hPeriod field test

end
end P0EFTJanusMappingTorusCutBulkGlobalBoundaryMeasure4D
end JanusFormal
