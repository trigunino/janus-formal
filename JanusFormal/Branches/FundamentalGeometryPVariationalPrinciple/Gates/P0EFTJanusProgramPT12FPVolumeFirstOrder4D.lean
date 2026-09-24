import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FPSmoothWeightProduct4D

namespace JanusFormal.P0EFTJanusProgramPT12FPVolumeFirstOrder4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

open P0EFTJanusProgramPT12FPSmoothWeightProduct4D
open P0EFTJanusScalarStressCovariantJetConservation4D

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
variable (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2)
variable (patch : SmoothHolonomicFrameChart4 period hPeriod)
variable (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)

/-- Explicit lower-order correction, with all coefficients determined by the actual metric. -/
def fpVolumeCorrectionLocal : Real :=
  globalMetricVolumeRatio period hPeriod metric (patch.coordinateMap coordinate) *
    (ghost (patch.coordinateMap coordinate) component *
      covariantScalarJetWave (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch
          (inverseSmoothMetricRatio period hPeriod metric) coordinate) +
      2 * covariantScalarGradientPairing
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch
          (inverseSmoothMetricRatio period hPeriod metric) coordinate)
        (localCovariantScalarJet period hPeriod metric patch
          (ghostComponent period hPeriod ghost component) coordinate))

theorem canonicalFPFormalAdjoint_eq_fp_add_firstOrder :
    canonicalFPFormalAdjoint period hPeriod metric ghost (patch.coordinateMap coordinate) component =
      globalGeneralMetricAbelianFaddeevPopov period hPeriod metric ghost (patch.coordinateMap coordinate) component +
        fpVolumeCorrectionLocal period hPeriod metric ghost component patch coordinate := by
  rw [canonicalFPFormalAdjoint_apply, fp_smoothGaugeWeight_apply_local]
  have hRatio := (globalMetricVolumeRatio_pos period hPeriod metric (patch.coordinateMap coordinate)).ne'
  unfold fpVolumeCorrectionLocal
  change _ * ((_ )⁻¹ * _ + _ + _) = _
  rw [mul_add, mul_add, ← mul_assoc, mul_inv_cancel₀ hRatio, one_mul]
  ring

/-- No second derivative of the ghost enters the canonical-volume correction. -/
theorem fpVolumeCorrectionLocal_eq_of_firstJet
    (other : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (hValue : ghost (patch.coordinateMap coordinate) component = other (patch.coordinateMap coordinate) component)
    (hGradient :
      (localCovariantScalarJet period hPeriod metric patch
        (ghostComponent period hPeriod ghost component) coordinate).gradient =
      (localCovariantScalarJet period hPeriod metric patch
        (ghostComponent period hPeriod other component) coordinate).gradient) :
    fpVolumeCorrectionLocal period hPeriod metric ghost component patch coordinate =
      fpVolumeCorrectionLocal period hPeriod metric other component patch coordinate := by
  unfold fpVolumeCorrectionLocal covariantScalarGradientPairing
  rw [hValue, hGradient]

end
end JanusFormal.P0EFTJanusProgramPT12FPVolumeFirstOrder4D
