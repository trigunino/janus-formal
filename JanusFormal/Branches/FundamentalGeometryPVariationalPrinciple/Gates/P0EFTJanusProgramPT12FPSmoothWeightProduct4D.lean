import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D

/-! The actual variable-metric FP product rule and its canonical-volume adjoint correction. -/
namespace JanusFormal.P0EFTJanusProgramPT12FPSmoothWeightProduct4D
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

theorem ghostComponent_smoothGaugeWeight
    (weight : SmoothScalarField period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
    ghostComponent period hPeriod (smoothGaugeWeight period hPeriod weight ghost) component =
      smoothScalarFieldMul period hPeriod weight (ghostComponent period hPeriod ghost component) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact (EuclideanSpace.proj component).map_smul (weight point) (ghost point)

theorem fp_smoothGaugeWeight_apply_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (weight : SmoothScalarField period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    globalGeneralMetricAbelianFaddeevPopov period hPeriod metric
        (smoothGaugeWeight period hPeriod weight ghost) (patch.coordinateMap coordinate) component =
      weight (patch.coordinateMap coordinate) *
        globalGeneralMetricAbelianFaddeevPopov period hPeriod metric ghost (patch.coordinateMap coordinate) component +
      ghost (patch.coordinateMap coordinate) component *
        P0EFTJanusScalarStressCovariantJetConservation4D.covariantScalarJetWave
          (localFixedSignMetric period hPeriod metric patch coordinate)
          (localCovariantScalarJet period hPeriod metric patch weight coordinate) +
      2 * covariantScalarGradientPairing
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch weight coordinate)
        (localCovariantScalarJet period hPeriod metric patch
          (ghostComponent period hPeriod ghost component) coordinate) := by
  simp only [globalGeneralMetricAbelianFaddeevPopov_apply_local, ghostComponent_smoothGaugeWeight]
  exact localCovariantScalarWave_mul period hPeriod metric patch weight
    (ghostComponent period hPeriod ghost component) coordinate

end
end JanusFormal.P0EFTJanusProgramPT12FPSmoothWeightProduct4D
