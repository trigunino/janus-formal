import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Recovery4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Transport4D

/-! Actual Faddeev--Popov smooth core in zeroth-order regular-frame L². -/
namespace JanusFormal.P0EFTJanusProgramPT12FaddeevPopovL2Core4D
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

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

def fpGhostL2 : GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real] CartanGhostL2 period hPeriod where
  toFun ghost := regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference ghost.field)
  map_add' first second := by
    simp only [← regularGhostL2Recovery_actual period hPeriod reference reference.metric]
    exact ((regularGhostL2Recovery period hPeriod reference reference.metric).toLinearMap.comp
      (globalNormalizedVectorFrameL2LinearMap period hPeriod reference.metric)).map_add first.field second.field
  map_smul' scalar ghost := by
    simp only [← regularGhostL2Recovery_actual period hPeriod reference reference.metric]
    exact ((regularGhostL2Recovery period hPeriod reference reference.metric).toLinearMap.comp
      (globalNormalizedVectorFrameL2LinearMap period hPeriod reference.metric)).map_smul scalar ghost.field

theorem fpGhostL2_injective : Function.Injective (fpGhostL2 period hPeriod reference) := by
  intro first second h
  apply GlobalDiffeomorphismGhostField.ext
  apply globalNormalizedVectorFrameL2LinearMap_injective period hPeriod reference.metric
  have hTransport := congrArg (regularGhostL2Transport period hPeriod reference reference.metric) h
  change regularGhostL2Transport period hPeriod reference reference.metric
    (regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference first.field)) =
    regularGhostL2Transport period hPeriod reference reference.metric
      (regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference second.field)) at hTransport
  simpa only [regularGhostL2Transport_actual] using hTransport

theorem fpGhostL2_denseRange : DenseRange (fpGhostL2 period hPeriod reference) := by
  apply (regularFrameGhostL2_denseRange period hPeriod).mono
  rintro _ ⟨coefficients, rfl⟩
  refine ⟨⟨regularFrameGhostFromCoefficients period hPeriod reference coefficients⟩, ?_⟩
  change regularFrameGhostL2 period hPeriod
    (regularFrameCartanGhostCoefficient period hPeriod reference
      (regularFrameGhostFromCoefficients period hPeriod reference coefficients)) = _
  rw [regularFrameGhostCoefficients_reconstructed]

def fpSmoothRowLinearMap (row : Fin 4) :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real] SmoothScalarField period hPeriod where
  toFun ghost := fpSmoothRow period hPeriod reference metric ghost.field row
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change fpSmoothRow period hPeriod reference metric (first + second).field row point =
      fpSmoothRow period hPeriod reference metric first.field row point +
        fpSmoothRow period hPeriod reference metric second.field row point
    rw [fpSmoothRow_actual, fpSmoothRow_actual, fpSmoothRow_actual]
    exact congrArg (fun covector => covector point (reference.frame row point))
      ((globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric).map_add first second)
  map_smul' scalar ghost := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change fpSmoothRow period hPeriod reference metric (scalar • ghost).field row point =
      scalar * fpSmoothRow period hPeriod reference metric ghost.field row point
    rw [fpSmoothRow_actual, fpSmoothRow_actual]
    exact congrArg (fun covector => covector point (reference.frame row point))
      ((globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric).map_smul scalar ghost)

def fpSmoothL2 : GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real] CartanGhostL2 period hPeriod where
  toFun ghost := WithLp.toLp 2 fun row => smoothToCanonicalPhysicalBulkL2 period hPeriod
    (fpSmoothRowLinearMap period hPeriod reference metric row ghost)
  map_add' first second := by
    apply PiLp.ext
    intro row
    exact ((smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
      (fpSmoothRowLinearMap period hPeriod reference metric row)).map_add first second
  map_smul' scalar ghost := by
    apply PiLp.ext
    intro row
    exact ((smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
      (fpSmoothRowLinearMap period hPeriod reference metric row)).map_smul scalar ghost

private def fpSmoothEquivDomain : GlobalDiffeomorphismGhostField period hPeriod ≃ₗ[Real]
    (fpGhostL2 period hPeriod reference).range :=
  LinearEquiv.ofInjective (fpGhostL2 period hPeriod reference) (fpGhostL2_injective period hPeriod reference)

def fpL2Core : CartanGhostL2 period hPeriod →ₗ.[Real] CartanGhostL2 period hPeriod where
  domain := (fpGhostL2 period hPeriod reference).range
  toFun := (fpSmoothL2 period hPeriod reference metric).comp
    (fpSmoothEquivDomain period hPeriod reference).symm.toLinearMap

theorem fpL2Core_smooth (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    fpL2Core period hPeriod reference metric ⟨fpGhostL2 period hPeriod reference ghost, ⟨ghost, rfl⟩⟩ =
      fpSmoothL2 period hPeriod reference metric ghost := by
  change fpSmoothL2 period hPeriod reference metric
    ((fpSmoothEquivDomain period hPeriod reference).symm ((fpSmoothEquivDomain period hPeriod reference) ghost)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem fpL2Core_pairing (field : (fpL2Core period hPeriod reference metric).domain)
    (row : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (fpL2Core period hPeriod reference metric field row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real field.val (fpRowAdjointTest period hPeriod reference metric row test) := by
  rcases field with ⟨field, hField⟩
  obtain ⟨ghost, rfl⟩ := hField
  rw [fpL2Core_smooth]
  exact fpSmoothRow_pairing period hPeriod reference metric ghost.field row test

end
end JanusFormal.P0EFTJanusProgramPT12FaddeevPopovL2Core4D
