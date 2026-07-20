import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeHolonomicGlobalCutoffPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricTangentialCompensation4D

/-!
# Invariant bridge from local cutoff divergence to the metric decomposition
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeLocalGlobalCutoffDivergenceMetricBridge4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D
open P0EFTJanusMappingTorusCanonicalLatitudeHolonomicGlobalCutoffPullback4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffGreenNormalTangentialSplit4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCutBulkCutoffGreenCurrentNormalFluxBridge4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricNormalDivergence4D
open P0EFTJanusMappingTorusCutBulkSmoothCutoffGreenMetricTangentialCompensation4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := Fin 4 → Real

/-- The invariant local divergence equals the established metric-normal term
plus its Jacobian compensation. No coordinate-dependent identification of the
two summands is required. -/
theorem localActualCenteredGlobalCutoffGreenCoordinateDivergence_eq_metricNormal_add_compensation
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
    localActualCutoffScalarGreenCoordinateDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test
        (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
          period hPeriod normal baseMap) 0 =
      canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence period hPeriod
          massSquared field test (base, normal) +
        canonicalCutBulkSmoothCutoffGreenMetricTangentialCompensation period hPeriod
          field test base normal := by
  rw [localActualCenteredGlobalCutoffGreenCoordinateDivergence_eq_normalCurrent_of_free
    period hPeriod base normal hNormal chart baseMap field test hFree]
  rw [← canonicalCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
    period hPeriod field test base normal ⟨hNormal.1.le, hNormal.2.le⟩]
  exact (metricNormalDivergence_add_tangentialCompensation_eq_cutoffGradientFlux_of_euler
    period hPeriod massSquared field test hField hTest base normal hNormal).symm

theorem localNormal_add_tangentialDivergence_eq_metricNormal_add_compensation
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
    localActualCutoffScalarGreenCoordinateNormalDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test
        (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
          period hPeriod normal baseMap) 0 +
      localActualCutoffScalarGreenCoordinateTangentialDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test
        (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
          period hPeriod normal baseMap) 0 =
      canonicalCutBulkSmoothCutoffGreenMetricNormalDivergence period hPeriod
          massSquared field test (base, normal) +
        canonicalCutBulkSmoothCutoffGreenMetricTangentialCompensation period hPeriod
          field test base normal := by
  rw [← localActualCutoffScalarGreenCoordinateDivergence_eq_normal_add_tangential]
  exact localActualCenteredGlobalCutoffGreenCoordinateDivergence_eq_metricNormal_add_compensation
    period hPeriod massSquared field test hField hTest base normal hNormal chart
      baseMap hFree

end
end P0EFTJanusMappingTorusCanonicalLatitudeLocalGlobalCutoffDivergenceMetricBridge4D
end JanusFormal
