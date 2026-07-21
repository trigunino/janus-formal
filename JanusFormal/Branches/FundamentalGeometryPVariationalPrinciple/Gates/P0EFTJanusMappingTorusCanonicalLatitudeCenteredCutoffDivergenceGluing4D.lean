import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeLocalGlobalCutoffDivergenceMetricBridge4D

/-!
# Gluing of centered canonical-collar cutoff-divergence representatives
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceGluing4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D
open P0EFTJanusMappingTorusCanonicalLatitudeHolonomicGlobalCutoffPullback4D
open P0EFTJanusMappingTorusCanonicalLatitudeLocalGlobalCutoffDivergenceMetricBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricNormalDivergence4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricTangentialCompensation4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := Fin 4 → Real

/-- Global canonical-collar value represented by every centered adapted chart. -/
def canonicalLatitudeCenteredGlobalCutoffDivergence
    (massSquared : Real) (field test : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence period hPeriod
      massSquared field test (base, normal) +
    canonicalCutBulkSmoothCutoffGreenMetricTangentialCompensation period hPeriod
      field test base normal

theorem canonicalLatitudeCenteredGlobalCutoffDivergence_eq_local
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
    canonicalLatitudeCenteredGlobalCutoffDivergence period hPeriod massSquared
        field test base normal =
      localActualCutoffScalarGreenCoordinateDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test
        (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
          period hPeriod normal baseMap) 0 := by
  exact (localActualCenteredGlobalCutoffGreenCoordinateDivergence_eq_metricNormal_add_compensation
    period hPeriod massSquared field test hField hTest base normal hNormal chart
      baseMap hFree).symm

/-- Any two centered adapted representatives at the same collar point agree,
without a transition-jet hypothesis. -/
theorem localCenteredGlobalCutoffDivergence_independent
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Ioo (0 : Real) 1)
    (firstChart secondChart :
      NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (firstBaseMap secondBaseMap : Vector4 → CanonicalLatitudeBase)
    (hFirstFree : localActualScalarGreenCoordinateDivergence period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (firstChart.toSmoothHolonomicFrameChart4 period hPeriod) field test 0 = 0)
    (hSecondFree : localActualScalarGreenCoordinateDivergence period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (secondChart.toSmoothHolonomicFrameChart4 period hPeriod) field test 0 = 0) :
    localActualCutoffScalarGreenCoordinateDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (firstChart.toSmoothHolonomicFrameChart4 period hPeriod) field test
        (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
          period hPeriod normal firstBaseMap) 0 =
      localActualCutoffScalarGreenCoordinateDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (secondChart.toSmoothHolonomicFrameChart4 period hPeriod) field test
        (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
          period hPeriod normal secondBaseMap) 0 := by
  rw [← canonicalLatitudeCenteredGlobalCutoffDivergence_eq_local
      period hPeriod massSquared field test hField hTest base normal hNormal
      firstChart firstBaseMap hFirstFree,
    ← canonicalLatitudeCenteredGlobalCutoffDivergence_eq_local
      period hPeriod massSquared field test hField hTest base normal hNormal
      secondChart secondBaseMap hSecondFree]

end
end P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceGluing4D
end JanusFormal
