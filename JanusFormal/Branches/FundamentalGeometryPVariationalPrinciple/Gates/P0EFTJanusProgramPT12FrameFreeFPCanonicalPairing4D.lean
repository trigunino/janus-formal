import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeLorenzGlobalStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D

/-! Actual FP adjunction in canonical volume, without a global tangent basis. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12FrameFreeLorenzGlobalStokes4D

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

theorem frameFreeCanonicalFPFormalAdjoint_component_pairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
    (∫ point, globalGeneralMetricAbelianFaddeevPopov period hPeriod metric field point component *
        test point component ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      ∫ point, field point component * canonicalFPFormalAdjoint period hPeriod metric test point component
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  let scaled := smoothGaugeWeight period hPeriod (inverseSmoothMetricRatio period hPeriod metric) test
  have hSym := frameFreeGlobalFP_component_metric_symmetry period hPeriod metric scaled field component
  rw [integral_generalLorentzVolumeMeasure_eq_reference,
    integral_generalLorentzVolumeMeasure_eq_reference] at hSym
  calc
    _ = ∫ point, globalMetricVolumeRatio period hPeriod metric point *
        (scaled point component * globalGeneralMetricAbelianFaddeevPopov
          period hPeriod metric field point component)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      apply integral_congr_ae
      filter_upwards [] with point
      change _ = globalMetricVolumeRatio period hPeriod metric point *
        ((globalMetricVolumeRatio period hPeriod metric point)⁻¹ * test point component * _)
      field_simp [(globalMetricVolumeRatio_pos period hPeriod metric point).ne']
    _ = _ := hSym.trans (integral_congr_ae (Filter.Eventually.of_forall (fun point => by
      rw [canonicalFPFormalAdjoint_apply]
      change _ = field point component * (globalMetricVolumeRatio period hPeriod metric point * _)
      ring)))

theorem frameFreePairedFPCanonicalAdjoint_pairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (field test : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real (globalPairedAbelianFPL2LinearMap period hPeriod metric field)
        (globalPairedGaugeLieL2LinearMap period hPeriod test) =
      inner Real (globalPairedGaugeLieL2LinearMap period hPeriod field)
        (pairedFPCanonicalAdjointL2 period hPeriod metric test) := by
  change inner Real (globalPairedGaugeLieL2LinearMap period hPeriod
    (fun sector => globalGeneralMetricAbelianFaddeevPopov period hPeriod (metric sector) (field sector)))
      (globalPairedGaugeLieL2LinearMap period hPeriod test) =
    inner Real (globalPairedGaugeLieL2LinearMap period hPeriod field)
      (globalPairedGaugeLieL2LinearMap period hPeriod
        (fun sector => canonicalFPFormalAdjoint period hPeriod (metric sector) (test sector)))
  rw [globalPairedGaugeLieL2_inner_eq_sum_integral, globalPairedGaugeLieL2_inner_eq_sum_integral]
  apply Finset.sum_congr rfl
  intro sector _
  unfold globalGaugeLiePairingAt
  rw [integral_finsetSum Finset.univ (fun component _ =>
    globalGaugeLieComponentProduct_integrable period hPeriod _ _ component),
    integral_finsetSum Finset.univ (fun component _ =>
      globalGaugeLieComponentProduct_integrable period hPeriod _ _ component)]
  apply Finset.sum_congr rfl
  intro component _
  exact frameFreeCanonicalFPFormalAdjoint_component_pairing period hPeriod
    (metric sector) (field sector) (test sector) component

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D
