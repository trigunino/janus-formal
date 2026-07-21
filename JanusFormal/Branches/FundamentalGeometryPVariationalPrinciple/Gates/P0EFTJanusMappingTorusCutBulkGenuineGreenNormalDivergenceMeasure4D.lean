import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D

/-!
# Genuine normal-divergence measure of the cut-bulk Green current
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGenuineGreenNormalDivergenceMeasure4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance bulkMeasurableSpace :
    MeasurableSpace (PositiveHemisphereCutBulk period hPeriod) := borel _

local instance bulkBorelSpace :
    BorelSpace (PositiveHemisphereCutBulk period hPeriod) where
  measurable_eq := rfl

/-- Source-collar density given by the actual normal derivative in the
interior, with the already smooth canonical density on the two faces. -/
def canonicalCutBulkGenuineGreenNormalDivergenceDensity
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter) : Real :=
  if parameter.2 ∈ Set.Ioo (0 : Real) 1 then
    deriv (fun normal => canonicalLatitudeCollarCutoff normal *
      canonicalCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test parameter.1 normal) parameter.2
  else
    canonicalCutBulkDivergenceDensity period hPeriod massSquared field test parameter

/-- The actual interior derivative extends to exactly the established smooth
canonical divergence density. -/
theorem canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_canonical
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalCutBulkGenuineGreenNormalDivergenceDensity period hPeriod
        massSquared field test parameter =
      canonicalCutBulkDivergenceDensity period hPeriod massSquared field test parameter := by
  unfold canonicalCutBulkGenuineGreenNormalDivergenceDensity
  split_ifs with hInterior
  · exact (cutoff_mul_canonicalCutBulkIntrinsicGreenNormalFlux_hasDerivAt
      period hPeriod massSquared field test parameter.1 parameter.2 hInterior).deriv
  · rfl

/-- Global pushed measure built from the actual normal derivative density. -/
def cutBulkGenuineGreenNormalDivergenceMeasure
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    VectorMeasure (PositiveHemisphereCutBulk period hPeriod) Real :=
  ((canonicalLatitudeCollarMeasure period).withDensityᵥ
      (canonicalCutBulkGenuineGreenNormalDivergenceDensity period hPeriod
        massSquared field test)).map
    (canonicalLatitudeCutBulkCollarMap period hPeriod)

theorem cutBulkGenuineGreenNormalDivergenceMeasure_eq_canonical
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGenuineGreenNormalDivergenceMeasure period hPeriod
        massSquared field test =
      cutBulkCanonicalDivergenceMeasure period hPeriod massSquared field test := by
  unfold cutBulkGenuineGreenNormalDivergenceMeasure
    cutBulkCanonicalDivergenceMeasure
  congr 2
  funext parameter
  exact canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_canonical
    period hPeriod massSquared field test parameter

/-- Two-sheet measured Stokes for the global measure whose interior density is
the genuine normal derivative of cutoff times the true vector-current flux. -/
theorem two_mul_cutBulkGenuineGreenNormalDivergenceMeasure_univ_eq_neg_flux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * cutBulkGenuineGreenNormalDivergenceMeasure period hPeriod
        massSquared field test Set.univ =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) := by
  rw [cutBulkGenuineGreenNormalDivergenceMeasure_eq_canonical,
    two_mul_cutBulkCanonicalDivergenceMeasure_univ_eq_neg_genuineFlux]

end
end P0EFTJanusMappingTorusCutBulkGenuineGreenNormalDivergenceMeasure4D
end JanusFormal
