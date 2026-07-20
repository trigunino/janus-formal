import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothCutoffScalarGreenCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGenuineGreenNormalDivergenceMeasure4D

/-!
# Normal-divergence measure of the genuine global cutoff Green current
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenNormalDivergenceMeasure4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkIntrinsicMetricVolumeDensity4D
open P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenNormalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffScalarGreenCurrent4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance bulkMeasurableSpace :
    MeasurableSpace (PositiveHemisphereCutBulk period hPeriod) := borel _

local instance bulkBorelSpace :
    BorelSpace (PositiveHemisphereCutBulk period hPeriod) where
  measurable_eq := rfl

/-- Normal flux of the genuine global vector field `χJ`. -/
def canonicalCutBulkSmoothCutoffGreenNormalFlux
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  let point := canonicalLatitudeCutBulkCollarMap period hPeriod (base, normal)
  (intrinsicCutBulkSmoothGeneralLorentzMetric period hPeriod).musical point
    (intrinsicCutBulkSmoothCutoffScalarGreenCurrent period hPeriod field test point)
    ((cutBulkToAmbientDerivativeEquiv period hPeriod point).symm
      (canonicalLatitudeNormalVector period hPeriod base normal))

theorem canonicalCutBulkSmoothCutoffGreenNormalFlux_eq_scalarCurrent
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Icc (0 : Real) 1) :
    canonicalCutBulkSmoothCutoffGreenNormalFlux period hPeriod field test
        base normal =
      cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base normal) :=
  intrinsicCutBulkSmoothCutoffScalarGreenCurrent_canonicalNormalFlux
    period hPeriod field test base normal hNormal

/-- Its actual normal derivative is the established canonical divergence
density throughout the collar interior. -/
theorem canonicalCutBulkSmoothCutoffGreenNormalFlux_hasDerivAt
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    HasDerivAt
      (canonicalCutBulkSmoothCutoffGreenNormalFlux period hPeriod field test base)
      (cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
        field test base normal) normal := by
  have hEventually : Filter.EventuallyEq (nhds normal)
      (canonicalCutBulkSmoothCutoffGreenNormalFlux period hPeriod field test base)
      (fun current => cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarPath period hPeriod base current)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hNormal] with current hCurrent
    exact canonicalCutBulkSmoothCutoffGreenNormalFlux_eq_scalarCurrent
      period hPeriod field test base current ⟨hCurrent.1.le, hCurrent.2.le⟩
  exact (cutBulkScalarCurrent_canonicalCollarPath_hasDerivAt period hPeriod
    massSquared field test base normal hNormal).congr_of_eventuallyEq hEventually

theorem deriv_canonicalCutBulkSmoothCutoffGreenNormalFlux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1) :
    deriv (canonicalCutBulkSmoothCutoffGreenNormalFlux period hPeriod field test base)
        normal =
      cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
        field test base normal :=
  (canonicalCutBulkSmoothCutoffGreenNormalFlux_hasDerivAt period hPeriod
    massSquared field test base normal hNormal).deriv

/-- Source-collar density expressed directly through the true global vector
field `χJ`, with the canonical smooth extension on both faces. -/
def canonicalCutBulkSmoothCutoffGreenNormalDivergenceDensity
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter) : Real :=
  if parameter.2 ∈ Set.Ioo (0 : Real) 1 then
    deriv (canonicalCutBulkSmoothCutoffGreenNormalFlux period hPeriod field test
      parameter.1) parameter.2
  else
    canonicalCutBulkDivergenceDensity period hPeriod massSquared field test parameter

theorem canonicalCutBulkSmoothCutoffGreenNormalDivergenceDensity_eq_canonical
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalCutBulkSmoothCutoffGreenNormalDivergenceDensity period hPeriod
        massSquared field test parameter =
      canonicalCutBulkDivergenceDensity period hPeriod massSquared field test parameter := by
  unfold canonicalCutBulkSmoothCutoffGreenNormalDivergenceDensity
  split_ifs with hInterior
  · exact deriv_canonicalCutBulkSmoothCutoffGreenNormalFlux period hPeriod
      massSquared field test parameter.1 parameter.2 hInterior
  · rfl

theorem canonicalCutBulkSmoothCutoffGreenNormalDivergenceDensity_eq_genuine
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalCutBulkSmoothCutoffGreenNormalDivergenceDensity period hPeriod
        massSquared field test parameter =
      canonicalCutBulkGenuineGreenNormalDivergenceDensity period hPeriod
        massSquared field test parameter := by
  rw [canonicalCutBulkSmoothCutoffGreenNormalDivergenceDensity_eq_canonical,
    canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_canonical]

def cutBulkSmoothCutoffGreenNormalDivergenceMeasure
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    VectorMeasure (PositiveHemisphereCutBulk period hPeriod) Real :=
  ((canonicalLatitudeCollarMeasure period).withDensityᵥ
      (canonicalCutBulkSmoothCutoffGreenNormalDivergenceDensity period hPeriod
        massSquared field test)).map
    (canonicalLatitudeCutBulkCollarMap period hPeriod)

theorem cutBulkSmoothCutoffGreenNormalDivergenceMeasure_eq_genuine
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkSmoothCutoffGreenNormalDivergenceMeasure period hPeriod
        massSquared field test =
      cutBulkGenuineGreenNormalDivergenceMeasure period hPeriod
        massSquared field test := by
  unfold cutBulkSmoothCutoffGreenNormalDivergenceMeasure
    cutBulkGenuineGreenNormalDivergenceMeasure
  congr 2
  funext parameter
  exact canonicalCutBulkSmoothCutoffGreenNormalDivergenceDensity_eq_genuine
    period hPeriod massSquared field test parameter

theorem two_mul_cutBulkSmoothCutoffGreenNormalDivergenceMeasure_univ_eq_neg_flux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * cutBulkSmoothCutoffGreenNormalDivergenceMeasure period hPeriod
        massSquared field test Set.univ =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) := by
  rw [cutBulkSmoothCutoffGreenNormalDivergenceMeasure_eq_genuine,
    two_mul_cutBulkGenuineGreenNormalDivergenceMeasure_univ_eq_neg_flux]

end
end P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenNormalDivergenceMeasure4D
end JanusFormal
