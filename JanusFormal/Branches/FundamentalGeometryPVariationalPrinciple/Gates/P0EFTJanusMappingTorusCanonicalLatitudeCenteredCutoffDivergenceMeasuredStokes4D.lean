import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkEqualMassEulerGreenNormalDivergence4D

/-!
# Measured Stokes for the glued centered cutoff divergence
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceMeasuredStokes4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D
open P0EFTJanusMappingTorusCanonicalLatitudeHolonomicGlobalCutoffPullback4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceGluing4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenNormalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkEqualMassEulerGreenNormalDivergence4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricTangentialCompensation4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := Fin 4 → Real

local instance bulkMeasurableSpace :
    MeasurableSpace (PositiveHemisphereCutBulk period hPeriod) := borel _

local instance bulkBorelSpace :
    BorelSpace (PositiveHemisphereCutBulk period hPeriod) where
  measurable_eq := rfl

/-- Interior glued local divergence, extended on both faces by the established
canonical density. -/
def canonicalLatitudeCenteredGlobalCutoffDivergenceDensity
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (parameter : CanonicalLatitudeCollarParameter) : Real :=
  if parameter.2 ∈ Ioo (0 : Real) 1 then
    canonicalLatitudeCenteredGlobalCutoffDivergence period hPeriod massSquared
      field test parameter.1 parameter.2
  else
    canonicalCutBulkDivergenceDensity period hPeriod massSquared field test parameter

theorem canonicalLatitudeCenteredGlobalCutoffDivergenceDensity_eq_local
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Ioo (0 : Real) 1)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (baseMap : Vector4 → CanonicalLatitudeBase)
    (hFree : localActualScalarGreenCoordinateDivergence period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test 0 = 0) :
    canonicalLatitudeCenteredGlobalCutoffDivergenceDensity period hPeriod
        massSquared field test (base, normal) =
      localActualCutoffScalarGreenCoordinateDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test
        (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
          period hPeriod normal baseMap) 0 := by
  rw [canonicalLatitudeCenteredGlobalCutoffDivergenceDensity, if_pos hNormal]
  exact canonicalLatitudeCenteredGlobalCutoffDivergence_eq_local period hPeriod
    massSquared field test hField hTest base normal hNormal chart baseMap hFree

theorem canonicalLatitudeCenteredGlobalCutoffDivergenceDensity_eq_genuine_of_euler
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalLatitudeCenteredGlobalCutoffDivergenceDensity period hPeriod
        massSquared field test parameter =
      canonicalCutBulkGenuineGreenNormalDivergenceDensity period hPeriod
        massSquared field test parameter := by
  unfold canonicalLatitudeCenteredGlobalCutoffDivergenceDensity
  split_ifs with hInterior
  · rw [canonicalCutBulkGenuineGreenNormalDivergenceDensity_eq_cutoffDerivative_mul_flux_of_euler
      period hPeriod massSquared field test hField hTest parameter
        ⟨hInterior.1.le, hInterior.2.le⟩]
    unfold canonicalLatitudeCenteredGlobalCutoffDivergence
    exact metricNormalDivergence_add_tangentialCompensation_eq_cutoffGradientFlux_of_euler
      period hPeriod massSquared field test hField hTest parameter.1 parameter.2
        hInterior
  · unfold canonicalCutBulkGenuineGreenNormalDivergenceDensity
    rw [if_neg hInterior]

/-- Pushed measure represented by the genuine local covariant divergence in
every centered adapted collar chart. -/
def cutBulkCanonicalLatitudeCenteredGlobalCutoffDivergenceMeasure
    (massSquared : Real) (field test : SmoothScalarField period hPeriod) :
    VectorMeasure (PositiveHemisphereCutBulk period hPeriod) Real :=
  ((canonicalLatitudeCollarMeasure period).withDensityᵥ
      (canonicalLatitudeCenteredGlobalCutoffDivergenceDensity period hPeriod
        massSquared field test)).map
    (canonicalLatitudeCutBulkCollarMap period hPeriod)

theorem cutBulkCanonicalLatitudeCenteredGlobalCutoffDivergenceMeasure_eq_genuine_of_euler
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    cutBulkCanonicalLatitudeCenteredGlobalCutoffDivergenceMeasure period hPeriod
        massSquared field test =
      cutBulkGenuineGreenNormalDivergenceMeasure period hPeriod
        massSquared field test := by
  unfold cutBulkCanonicalLatitudeCenteredGlobalCutoffDivergenceMeasure
    cutBulkGenuineGreenNormalDivergenceMeasure
  congr 2
  funext parameter
  exact canonicalLatitudeCenteredGlobalCutoffDivergenceDensity_eq_genuine_of_euler
    period hPeriod massSquared field test hField hTest parameter

theorem two_mul_cutBulkCanonicalLatitudeCenteredGlobalCutoffDivergenceMeasure_univ_eq_neg_flux
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    2 * cutBulkCanonicalLatitudeCenteredGlobalCutoffDivergenceMeasure period hPeriod
        massSquared field test Set.univ =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) := by
  rw [cutBulkCanonicalLatitudeCenteredGlobalCutoffDivergenceMeasure_eq_genuine_of_euler
      period hPeriod massSquared field test hField hTest,
    two_mul_cutBulkGenuineGreenNormalDivergenceMeasure_univ_eq_neg_flux]

end
end P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceMeasuredStokes4D
end JanusFormal
