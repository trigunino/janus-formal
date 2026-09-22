import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LorenzGlobalStokes4D

/-! The actual FP formal adjoint in the fixed canonical measure is r FP(r⁻¹ ·). -/
namespace JanusFormal.P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPT12LorenzGlobalStokes4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

def smoothGaugeWeight (weight : SmoothScalarField period hPeriod) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra →ₗ[Real]
      SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun field :=
    { toFun := fun point => weight point • field point
      contMDiff_toFun := weight.contMDiff_toFun.smul field.contMDiff_toFun }
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
    intro point
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
    intro point
    exact smul_comm _ _ _

def inverseSmoothMetricRatio (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := fun point => (globalMetricVolumeRatio period hPeriod metric point)⁻¹
  contMDiff_toFun := (globalSmoothMetricVolumeRatio period hPeriod metric).contMDiff_toFun.inv₀
    (fun point => (globalMetricVolumeRatio_pos period hPeriod metric point).ne')

/-- Smooth everywhere; the density is positive on the entire quotient. -/
def canonicalFPFormalAdjoint (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra →ₗ[Real]
      SmoothQuotientField period hPeriod GaugeLieAlgebra :=
  (smoothGaugeWeight period hPeriod (globalSmoothMetricVolumeRatio period hPeriod metric)).comp
    ((globalGeneralMetricAbelianFaddeevPopovLinearMap period hPeriod metric).comp
      (smoothGaugeWeight period hPeriod (inverseSmoothMetricRatio period hPeriod metric)))

theorem canonicalFPFormalAdjoint_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (test : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod) (component : Fin 2) :
    canonicalFPFormalAdjoint period hPeriod metric test point component =
      globalMetricVolumeRatio period hPeriod metric point *
        globalGeneralMetricAbelianFaddeevPopov period hPeriod metric
          (smoothGaugeWeight period hPeriod (inverseSmoothMetricRatio period hPeriod metric) test)
          point component := rfl

/-- Exact adjunction for the installed FP, now in the canonical volume. -/
theorem canonicalFPFormalAdjoint_component_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (field test : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
    (∫ point, globalGeneralMetricAbelianFaddeevPopov period hPeriod metric.metric field point component *
        test point component ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      ∫ point, field point component * canonicalFPFormalAdjoint period hPeriod metric.metric test point component
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  let scaled := smoothGaugeWeight period hPeriod (inverseSmoothMetricRatio period hPeriod metric.metric) test
  have hSym := globalFP_component_metric_symmetry period hPeriod metric scaled field component
  rw [integral_generalLorentzVolumeMeasure_eq_reference,
    integral_generalLorentzVolumeMeasure_eq_reference] at hSym
  calc
    _ = ∫ point, globalMetricVolumeRatio period hPeriod metric.metric point *
        (scaled point component * globalGeneralMetricAbelianFaddeevPopov
          period hPeriod metric.metric field point component)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      apply integral_congr_ae
      filter_upwards [] with point
      change _ = globalMetricVolumeRatio period hPeriod metric.metric point *
        ((globalMetricVolumeRatio period hPeriod metric.metric point)⁻¹ * test point component * _)
      field_simp [(globalMetricVolumeRatio_pos period hPeriod metric.metric point).ne']
    _ = _ := hSym.trans (integral_congr_ae (Filter.Eventually.of_forall (fun point => by
      rw [canonicalFPFormalAdjoint_apply]
      change _ = field point component * (globalMetricVolumeRatio period hPeriod metric.metric point * _)
      ring)))

end
end JanusFormal.P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
