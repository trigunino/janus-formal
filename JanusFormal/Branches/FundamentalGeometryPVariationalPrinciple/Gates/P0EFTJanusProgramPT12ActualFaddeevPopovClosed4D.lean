import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
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

/-! Closed paired Faddeev--Popov in the original L² completions, with a common smooth core. -/
namespace JanusFormal.P0EFTJanusProgramPT12ActualFaddeevPopovClosed4D
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

open P0EFTJanusProgramPT12ActualFaddeevPopovCore4D

theorem actualFPL2_closedGraph_pairing
    (pair : ActualFPGhostL2 period hPeriod reference metric × ActualPairedFPL2 period hPeriod)
    (hPair : pair ∈ (actualFPL2Core period hPeriod reference metric).graph.topologicalClosure)
    (sector : Sector) (row : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (actualFPCovectorRecovery period hPeriod reference (pair.2 sector) row)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real ((regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm pair.1)
      (fpRowAdjointTest period hPeriod reference (metric sector) row test) := by
  have hClosed : IsClosed {value : ActualFPGhostL2 period hPeriod reference metric × ActualPairedFPL2 period hPeriod |
      inner Real (actualFPCovectorRecovery period hPeriod reference (value.2 sector) row)
        (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real ((regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm value.1)
        (fpRowAdjointTest period hPeriod reference (metric sector) row test)} := by
    apply isClosed_eq <;> fun_prop
  apply (closure_minimal _ hClosed) hPair
  intro value hValue
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
  change inner Real (actualFPCovectorRecovery period hPeriod reference (value.2 sector) row) _ =
    inner Real ((regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm value.1) _
  rw [← hOutput, ← hInput]
  exact actualFPL2Core_pairing period hPeriod reference metric field sector row test

theorem actualFPL2Core_isClosable : (actualFPL2Core period hPeriod reference metric).IsClosable := by
  refine ⟨(actualFPL2Core period hPeriod reference metric).graph.topologicalClosure.toLinearPMap, ?_⟩
  symm
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨x, y⟩ hPair hZero
  change x = 0 at hZero
  subst x
  apply PiLp.ext
  intro sector
  apply actualFPCovectorRecovery_injective period hPeriod reference
  change actualFPCovectorRecovery period hPeriod reference (y sector) = actualFPCovectorRecovery period hPeriod reference 0
  rw [map_zero]
  apply PiLp.ext
  intro row
  apply (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod).eq_zero_of_inner_left (𝕜 := Real)
  intro test
  have h := actualFPL2_closedGraph_pairing period hPeriod reference metric (0, y) hPair sector row test
  simpa only [map_zero, inner_zero_left] using h

def actualFPL2Minimal : ActualFPGhostL2 period hPeriod reference metric →ₗ.[Real] ActualPairedFPL2 period hPeriod :=
  (actualFPL2Core period hPeriod reference metric).closure

theorem actualFPL2Minimal_graph :
    (actualFPL2Minimal period hPeriod reference metric).graph =
      (actualFPL2Core period hPeriod reference metric).graph.topologicalClosure :=
  (actualFPL2Core_isClosable period hPeriod reference metric).graph_closure_eq_closure_graph.symm

theorem actualFPL2Minimal_isClosed : (actualFPL2Minimal period hPeriod reference metric).IsClosed :=
  (actualFPL2Core_isClosable period hPeriod reference metric).closure_isClosed

theorem actualFPL2Minimal_hasCore : (actualFPL2Minimal period hPeriod reference metric).HasCore
    (actualFPGhostSmooth period hPeriod reference metric).range :=
  (actualFPL2Core period hPeriod reference metric).closureHasCore

theorem actualFPL2Minimal_denseDomain : Dense
    ((actualFPL2Minimal period hPeriod reference metric).domain : Set (ActualFPGhostL2 period hPeriod reference metric)) :=
  (actualFPGhostSmooth_denseRange period hPeriod reference metric).mono
    (fun _ h => (actualFPL2Core period hPeriod reference metric).le_closure.1 h)

theorem actualFPL2Minimal_smooth_mem (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    actualFPGhostSmooth period hPeriod reference metric ghost ∈ (actualFPL2Minimal period hPeriod reference metric).domain :=
  (actualFPL2Core period hPeriod reference metric).le_closure.1 ⟨ghost, rfl⟩

theorem actualFPL2Minimal_smooth (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    actualFPL2Minimal period hPeriod reference metric
      ⟨actualFPGhostSmooth period hPeriod reference metric ghost, actualFPL2Minimal_smooth_mem period hPeriod reference metric ghost⟩ =
      actualFPSmoothOutput period hPeriod metric ghost :=
  ((actualFPL2Core period hPeriod reference metric).le_closure.2 (x := ⟨_, ⟨ghost, rfl⟩⟩)
    (y := ⟨_, actualFPL2Minimal_smooth_mem period hPeriod reference metric ghost⟩) rfl).symm.trans
      (actualFPL2Core_smooth period hPeriod reference metric ghost)

def actualFPGraphRecovery
    (pair : ActualFPGhostL2 period hPeriod reference metric × ActualPairedFPL2 period hPeriod) :
    CartanGhostL2 period hPeriod × PairedFPL2 period hPeriod :=
  ((regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm pair.1,
    WithLp.toLp 2 fun sector => actualFPCovectorRecovery period hPeriod reference (pair.2 sector))

theorem actualFPGraphRecovery_continuous : Continuous (actualFPGraphRecovery period hPeriod reference metric) := by
  apply Continuous.prodMk
  · exact (regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm.continuous.comp continuous_fst
  · apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro sector
    exact (actualFPCovectorRecovery period hPeriod reference).continuous.comp
      ((PiLp.continuous_apply 2 _ sector).comp continuous_snd)

theorem actualFPGraphRecovery_smooth (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    actualFPGraphRecovery period hPeriod reference metric
      (actualFPGhostSmooth period hPeriod reference metric ghost, actualFPSmoothOutput period hPeriod metric ghost) =
      (fpGhostL2 period hPeriod reference ghost, pairedFPSmoothL2 period hPeriod reference metric ghost) := by
  apply Prod.ext
  · exact (regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm_apply_apply _
  · apply PiLp.ext
    intro sector
    exact actualFPCovectorRecovery_smooth period hPeriod reference metric ghost sector

theorem actualFPL2Minimal_recovery_mem_graph
    (pair : ActualFPGhostL2 period hPeriod reference metric × ActualPairedFPL2 period hPeriod)
    (hPair : pair ∈ (actualFPL2Minimal period hPeriod reference metric).graph) :
    actualFPGraphRecovery period hPeriod reference metric pair ∈ (pairedFPL2Minimal period hPeriod reference metric).graph := by
  rw [actualFPL2Minimal_graph] at hPair
  have hClosed := (pairedFPL2Minimal_isClosed period hPeriod reference metric).preimage
    (actualFPGraphRecovery_continuous period hPeriod reference metric)
  apply (closure_minimal _ hClosed) hPair
  intro value hValue
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
  rcases field with ⟨field, hField⟩
  obtain ⟨ghost, rfl⟩ := hField
  have hValueEq : value = (actualFPGhostSmooth period hPeriod reference metric ghost, actualFPSmoothOutput period hPeriod metric ghost) :=
    Prod.ext hInput.symm (hOutput.symm.trans (actualFPL2Core_smooth period hPeriod reference metric ghost))
  change actualFPGraphRecovery period hPeriod reference metric value ∈
    (pairedFPL2Minimal period hPeriod reference metric).graph
  rw [hValueEq, actualFPGraphRecovery_smooth]
  exact (LinearPMap.mem_graph_iff _).mpr
    ⟨⟨_, pairedFPL2Minimal_smooth_mem period hPeriod reference metric ghost⟩, rfl,
      pairedFPL2Minimal_smooth period hPeriod reference metric ghost⟩

end
end JanusFormal.P0EFTJanusProgramPT12ActualFaddeevPopovClosed4D
