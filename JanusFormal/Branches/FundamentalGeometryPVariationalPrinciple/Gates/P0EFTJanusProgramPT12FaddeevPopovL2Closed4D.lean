import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Recovery4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Transport4D

/-! Minimal closed actual Faddeev--Popov operator with its dense smooth graph core. -/
namespace JanusFormal.P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
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

open P0EFTJanusProgramPT12FaddeevPopovL2Core4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

theorem fpL2_closedGraph_pairing
    (pair : CartanGhostL2 period hPeriod × CartanGhostL2 period hPeriod)
    (hPair : pair ∈ (fpL2Core period hPeriod reference metric).graph.topologicalClosure)
    (row : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (pair.2 row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real pair.1 (fpRowAdjointTest period hPeriod reference metric row test) := by
  have hClosed : IsClosed {value : CartanGhostL2 period hPeriod × CartanGhostL2 period hPeriod |
      inner Real (value.2 row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
        inner Real value.1 (fpRowAdjointTest period hPeriod reference metric row test)} := by
    apply isClosed_eq <;> fun_prop
  apply (closure_minimal _ hClosed) hPair
  intro value hValue
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
  change inner Real (value.2 row) _ = inner Real value.1 _
  rw [← hOutput, ← hInput]
  exact fpL2Core_pairing period hPeriod reference metric field row test

theorem fpL2Core_isClosable : (fpL2Core period hPeriod reference metric).IsClosable := by
  refine ⟨(fpL2Core period hPeriod reference metric).graph.topologicalClosure.toLinearPMap, ?_⟩
  symm
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨x, y⟩ hPair hZero
  change x = 0 at hZero
  subst x
  apply PiLp.ext
  intro row
  apply (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod).eq_zero_of_inner_left (𝕜 := Real)
  intro test
  exact (fpL2_closedGraph_pairing period hPeriod reference metric (0, y) hPair row test).trans (inner_zero_left _)

def fpL2Minimal : CartanGhostL2 period hPeriod →ₗ.[Real] CartanGhostL2 period hPeriod :=
  (fpL2Core period hPeriod reference metric).closure

theorem fpL2Minimal_graph :
    (fpL2Minimal period hPeriod reference metric).graph =
      (fpL2Core period hPeriod reference metric).graph.topologicalClosure :=
  (fpL2Core_isClosable period hPeriod reference metric).graph_closure_eq_closure_graph.symm

theorem fpL2Minimal_isClosed : (fpL2Minimal period hPeriod reference metric).IsClosed :=
  (fpL2Core_isClosable period hPeriod reference metric).closure_isClosed

theorem fpL2Minimal_hasCore : (fpL2Minimal period hPeriod reference metric).HasCore
    (fpGhostL2 period hPeriod reference).range :=
  (fpL2Core period hPeriod reference metric).closureHasCore

theorem fpL2Minimal_denseDomain : Dense ((fpL2Minimal period hPeriod reference metric).domain : Set (CartanGhostL2 period hPeriod)) :=
  (fpGhostL2_denseRange period hPeriod reference).mono
    (fun _ h => (fpL2Core period hPeriod reference metric).le_closure.1 h)

theorem fpL2Minimal_smooth_mem (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    fpGhostL2 period hPeriod reference ghost ∈ (fpL2Minimal period hPeriod reference metric).domain :=
  (fpL2Core period hPeriod reference metric).le_closure.1 ⟨ghost, rfl⟩

theorem fpL2Minimal_smooth (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    fpL2Minimal period hPeriod reference metric
      ⟨fpGhostL2 period hPeriod reference ghost, fpL2Minimal_smooth_mem period hPeriod reference metric ghost⟩ =
      fpSmoothL2 period hPeriod reference metric ghost :=
  ((fpL2Core period hPeriod reference metric).le_closure.2 (x := ⟨_, ⟨ghost, rfl⟩⟩)
    (y := ⟨_, fpL2Minimal_smooth_mem period hPeriod reference metric ghost⟩) rfl).symm.trans
      (fpL2Core_smooth period hPeriod reference metric ghost)

def fpCovectorSingle (row : Fin 4) (test : SmoothScalarField period hPeriod) : CartanGhostL2 period hPeriod :=
  PiLp.single 2 row (smoothToCanonicalPhysicalBulkL2 period hPeriod test)

theorem fpCovectorSingle_pairing (field : CartanGhostL2 period hPeriod)
    (row : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real field (fpCovectorSingle period hPeriod row test) =
      inner Real (field row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) := by
  simp [fpCovectorSingle, PiLp.inner_apply, PiLp.single_apply, apply_ite]

theorem fpRowAdjointTest_mem_graph (row : Fin 4) (test : SmoothScalarField period hPeriod) :
    (fpCovectorSingle period hPeriod row test, fpRowAdjointTest period hPeriod reference metric row test) ∈
      (fpL2Minimal period hPeriod reference metric).adjoint.graph := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (fpL2Minimal_denseDomain period hPeriod reference metric),
    Submodule.mem_adjoint_iff]
  intro field output hGraph
  apply sub_eq_zero.mpr
  rw [fpCovectorSingle_pairing]
  exact fpL2_closedGraph_pairing period hPeriod reference metric (field, output)
    (by rw [← fpL2Minimal_graph]; exact hGraph) row test

end
end JanusFormal.P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
