import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFaddeevPopovClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Recovery4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Transport4D

/-! Actual paired Faddeev--Popov smooth graph in the original ghost and covector completions. -/
namespace JanusFormal.P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

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

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D


open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

open P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12DeDonderRowAdjoint4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

open P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
open P0EFTJanusProgramPT12RegularGhostL2Recovery4D
open P0EFTJanusProgramPT12RegularGhostL2Transport4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12FaddeevPopovL2Core4D
open P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

open P0EFTJanusProgramPT12FrameCovectorL2Transport4D
open P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
open P0EFTJanusProgramPT12RegularGhostL2Equiv4D
open P0EFTJanusProgramPT12PairedFaddeevPopovClosed4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

abbrev ActualFPGhostL2 := (regularGhostL2Transport period hPeriod reference (metric .plus)).range
abbrev ActualFPCovectorL2 := FrameCovectorL2Completion period hPeriod (finiteSmoothTangentFrame period hPeriod)
abbrev ActualPairedFPL2 := PiLp 2 fun _ : Sector => ActualFPCovectorL2 period hPeriod

def actualFPGhostSmooth : GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
    ActualFPGhostL2 period hPeriod reference metric :=
  (regularGhostL2EquivRange period hPeriod reference (metric .plus)).toLinearMap.comp
    (fpGhostL2 period hPeriod reference)

theorem actualFPGhostSmooth_original (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    (actualFPGhostSmooth period hPeriod reference metric ghost).val =
      globalNormalizedVectorFrameL2LinearMap period hPeriod (metric .plus) ghost.field :=
  regularGhostL2Transport_actual period hPeriod reference (metric .plus) ghost.field

theorem actualFPGhostSmooth_injective : Function.Injective (actualFPGhostSmooth period hPeriod reference metric) :=
  (regularGhostL2EquivRange period hPeriod reference (metric .plus)).injective.comp
    (fpGhostL2_injective period hPeriod reference)

theorem actualFPGhostSmooth_denseRange : DenseRange (actualFPGhostSmooth period hPeriod reference metric) :=
  (regularGhostL2EquivRange period hPeriod reference (metric .plus)).surjective.denseRange.comp
    (fpGhostL2_denseRange period hPeriod reference)
    (regularGhostL2EquivRange period hPeriod reference (metric .plus)).continuous

def actualFPCovectorRecovery : ActualFPCovectorL2 period hPeriod →L[Real] CartanGhostL2 period hPeriod :=
  (frameCovectorL2Space period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)).subtypeL.comp
      (frameCovectorL2Equiv period hPeriod (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
        (finiteSmoothTangentFrame period hPeriod) reference.metric).symm.toContinuousLinearMap

theorem actualFPCovectorRecovery_injective : Function.Injective (actualFPCovectorRecovery period hPeriod reference) := by
  intro first second h
  apply (frameCovectorL2Equiv period hPeriod (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
    (finiteSmoothTangentFrame period hPeriod) reference.metric).symm.injective
  exact Subtype.ext h

def actualFPSmoothOutput : GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real] ActualPairedFPL2 period hPeriod where
  toFun ghost := WithLp.toLp 2 fun sector => frameCovectorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)
    (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod (metric sector) ghost)
  map_add' first second := by
    apply PiLp.ext
    intro sector
    exact ((frameCovectorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)).comp
      (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod (metric sector))).map_add first second
  map_smul' scalar ghost := by
    apply PiLp.ext
    intro sector
    exact ((frameCovectorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)).comp
      (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod (metric sector))).map_smul scalar ghost

theorem actualFPSmoothOutput_original (ghost : GlobalDiffeomorphismGhostField period hPeriod) (sector : Sector) :
    (actualFPSmoothOutput period hPeriod metric ghost sector).val =
      globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod (metric sector)
        (globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap period hPeriod (metric sector) ghost) := rfl

theorem actualFPCovectorRecovery_smooth (ghost : GlobalDiffeomorphismGhostField period hPeriod) (sector : Sector) :
    actualFPCovectorRecovery period hPeriod reference (actualFPSmoothOutput period hPeriod metric ghost sector) =
      fpSmoothL2 period hPeriod reference (metric sector) ghost := by
  change frameCovectorL2Transport period hPeriod (finiteSmoothTangentFrame period hPeriod)
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) reference.metric
      (frameCovectorL2 period hPeriod (finiteSmoothTangentFrame period hPeriod)
        (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod (metric sector) ghost)) = _
  rw [frameCovectorL2Transport_smooth]
  apply PiLp.ext
  intro row
  apply congrArg (smoothToCanonicalPhysicalBulkL2 period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact (fpSmoothRow_actual period hPeriod reference (metric sector) ghost row point).symm

private def actualFPSmoothEquivDomain : GlobalDiffeomorphismGhostField period hPeriod ≃ₗ[Real]
    (actualFPGhostSmooth period hPeriod reference metric).range :=
  LinearEquiv.ofInjective (actualFPGhostSmooth period hPeriod reference metric)
    (actualFPGhostSmooth_injective period hPeriod reference metric)

def actualFPL2Core : ActualFPGhostL2 period hPeriod reference metric →ₗ.[Real] ActualPairedFPL2 period hPeriod where
  domain := (actualFPGhostSmooth period hPeriod reference metric).range
  toFun := (actualFPSmoothOutput period hPeriod metric).comp
    (actualFPSmoothEquivDomain period hPeriod reference metric).symm.toLinearMap

theorem actualFPL2Core_smooth (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    actualFPL2Core period hPeriod reference metric
      ⟨actualFPGhostSmooth period hPeriod reference metric ghost, ⟨ghost, rfl⟩⟩ =
      actualFPSmoothOutput period hPeriod metric ghost := by
  change actualFPSmoothOutput period hPeriod metric
    ((actualFPSmoothEquivDomain period hPeriod reference metric).symm
      ((actualFPSmoothEquivDomain period hPeriod reference metric) ghost)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem actualFPL2Core_pairing (field : (actualFPL2Core period hPeriod reference metric).domain)
    (sector : Sector) (row : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (actualFPCovectorRecovery period hPeriod reference (actualFPL2Core period hPeriod reference metric field sector) row)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real ((regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm field.val)
      (fpRowAdjointTest period hPeriod reference (metric sector) row test) := by
  rcases field with ⟨field, hField⟩
  obtain ⟨ghost, rfl⟩ := hField
  rw [actualFPL2Core_smooth, actualFPCovectorRecovery_smooth]
  change inner Real (fpSmoothL2 period hPeriod reference (metric sector) ghost row) _ =
    inner Real ((regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm
      ((regularGhostL2EquivRange period hPeriod reference (metric .plus)) (fpGhostL2 period hPeriod reference ghost))) _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact fpSmoothRow_pairing period hPeriod reference (metric sector) ghost.field row test

end
end JanusFormal.P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
