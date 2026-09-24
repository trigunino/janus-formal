import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FPIntrinsicFirstOrder4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalDirectionalH1L24D

/-! The actual FP volume correction extends boundedly from ten-flow H¹ to L². -/
namespace JanusFormal.P0EFTJanusProgramPT12FPVolumeH1Bound4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12FPIntrinsicFirstOrder4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPT12CanonicalDirectionalH1L24D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

variable (metric : RegularGeneralLorentzMetric period hPeriod)

def fpVolumeCorrectionSmooth : SmoothScalarField period hPeriod →ₗ[Real]
    SmoothScalarField period hPeriod :=
  (canonicalScalarMul period hPeriod (globalSmoothMetricVolumeRatio period hPeriod metric.metric)).comp
    (canonicalScalarMul period hPeriod (actualFPScalarWave period hPeriod metric.metric
      (inverseSmoothMetricRatio period hPeriod metric.metric)) +
    (2 : Real) • canonicalDirectionalDerivativeSmooth period hPeriod metric
      (actualFPScalarGradient period hPeriod metric.metric
        (inverseSmoothMetricRatio period hPeriod metric.metric)))

theorem fpVolumeCorrectionSmooth_eq_actual
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
    fpVolumeCorrectionSmooth period hPeriod metric (ghostComponent period hPeriod ghost component) =
      ghostComponent period hPeriod (canonicalFPFormalAdjoint period hPeriod metric.metric ghost) component -
      ghostComponent period hPeriod
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod metric.metric ghost) component := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change globalMetricVolumeRatio period hPeriod metric.metric point *
    (actualFPScalarWave period hPeriod metric.metric
      (inverseSmoothMetricRatio period hPeriod metric.metric) point * ghost point component +
    2 * canonicalDirectionalDerivativeSmooth period hPeriod metric
      (actualFPScalarGradient period hPeriod metric.metric
        (inverseSmoothMetricRatio period hPeriod metric.metric))
      (ghostComponent period hPeriod ghost component) point) =
    canonicalFPFormalAdjoint period hPeriod metric.metric ghost point component -
      globalGeneralMetricAbelianFaddeevPopov period hPeriod metric.metric ghost point component
  rw [canonicalDirectionalDerivativeSmooth_apply,
    canonicalFPFormalAdjoint_eq_intrinsic_firstOrder]
  change _ * (_ * _ + 2 * scalarDifferential period hPeriod
    (ghostComponent period hPeriod ghost component) point _) = _
  ring

/-- No closed-range or spectral-gap hypothesis enters this bounded extension. -/
def fpVolumeCorrectionH1ToL2 : CanonicalTenFlowScalarH1 period hPeriod →L[Real]
    CanonicalPhysicalBulkL2 period hPeriod :=
  (canonicalSmoothMultiplier period hPeriod (globalSmoothMetricVolumeRatio period hPeriod metric.metric)).comp
    ((canonicalSmoothMultiplier period hPeriod (actualFPScalarWave period hPeriod metric.metric
      (inverseSmoothMetricRatio period hPeriod metric.metric))).comp
        (h1GraphToL2 period hPeriod Real (canonicalTenFlowFrame period hPeriod)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
    (2 : Real) • canonicalDirectionalH1ToL2 period hPeriod metric
      (actualFPScalarGradient period hPeriod metric.metric
        (inverseSmoothMetricRatio period hPeriod metric.metric)))

theorem fpVolumeCorrectionH1ToL2_smooth (field : SmoothScalarField period hPeriod) :
    fpVolumeCorrectionH1ToL2 period hPeriod metric
        (smoothToH1GraphLinearMap period hPeriod Real (canonicalTenFlowFrame period hPeriod)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (fpVolumeCorrectionSmooth period hPeriod metric field) := by
  simp only [fpVolumeCorrectionH1ToL2, ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    h1GraphToL2_agrees_on_smooth, canonicalDirectionalH1ToL2_smooth]
  change canonicalSmoothMultiplier period hPeriod _
    (canonicalSmoothMultiplier period hPeriod _ (smoothToCanonicalPhysicalBulkL2 period hPeriod field) +
      (2 : Real) • smoothToCanonicalPhysicalBulkL2 period hPeriod _) = _
  rw [canonicalSmoothMultiplier_smooth, ← map_smul, ← map_add, canonicalSmoothMultiplier_smooth]
  rfl

theorem fpVolumeCorrectionH1ToL2_actual
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
    fpVolumeCorrectionH1ToL2 period hPeriod metric
        (smoothToH1GraphLinearMap period hPeriod Real (canonicalTenFlowFrame period hPeriod)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          (ghostComponent period hPeriod ghost component)) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (ghostComponent period hPeriod (canonicalFPFormalAdjoint period hPeriod metric.metric ghost) component) -
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianFaddeevPopov period hPeriod metric.metric ghost) component) := by
  rw [fpVolumeCorrectionH1ToL2_smooth, fpVolumeCorrectionSmooth_eq_actual, map_sub]

theorem fpVolumeCorrectionH1ToL2_norm_le (field : CanonicalTenFlowScalarH1 period hPeriod) :
    ‖fpVolumeCorrectionH1ToL2 period hPeriod metric field‖ ≤
      ‖fpVolumeCorrectionH1ToL2 period hPeriod metric‖ * ‖field‖ :=
  (fpVolumeCorrectionH1ToL2 period hPeriod metric).le_opNorm field

theorem fpVolumeCorrection_actual_bound
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
    ‖smoothToCanonicalPhysicalBulkL2 period hPeriod
        (ghostComponent period hPeriod (canonicalFPFormalAdjoint period hPeriod metric.metric ghost) component) -
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianFaddeevPopov period hPeriod metric.metric ghost) component)‖ ≤
      ‖fpVolumeCorrectionH1ToL2 period hPeriod metric‖ *
        ‖smoothToH1GraphLinearMap period hPeriod Real (canonicalTenFlowFrame period hPeriod)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          (ghostComponent period hPeriod ghost component)‖ := by
  rw [← fpVolumeCorrectionH1ToL2_actual]
  exact fpVolumeCorrectionH1ToL2_norm_le period hPeriod metric _

end
end JanusFormal.P0EFTJanusProgramPT12FPVolumeH1Bound4D
