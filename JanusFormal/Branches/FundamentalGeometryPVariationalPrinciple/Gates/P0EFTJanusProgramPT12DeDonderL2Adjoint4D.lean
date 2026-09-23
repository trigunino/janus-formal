import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderL2Closed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorL2Bridge4D

/-! Hilbert adjoint tests for the actual closed de Donder operator. -/
namespace JanusFormal.P0EFTJanusProgramPT12DeDonderL2Adjoint4D
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
open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
open P0EFTJanusProgramPT12RegularTensorL2Bridge4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
variable (reference : RegularGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12DeDonderL2Closed4D

include reference in
theorem deDonderL2Minimal_graph :
    (deDonderL2Minimal period hPeriod metric).graph =
      (deDonderL2Core period hPeriod metric).graph.topologicalClosure :=
  (deDonderL2Core_isClosable period hPeriod metric reference).graph_closure_eq_closure_graph.symm

def deDonderCovectorSingle (row : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (test : SmoothScalarField period hPeriod) : GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  PiLp.single 2 row (smoothToCanonicalPhysicalBulkL2 period hPeriod test)

theorem deDonderCovectorSingle_pairing (field : GlobalGeneralMetricDeDonderFrameL2 period hPeriod)
    (row : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : SmoothScalarField period hPeriod) :
    inner Real field (deDonderCovectorSingle period hPeriod row test) =
      inner Real (field row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) := by
  simp [deDonderCovectorSingle, PiLp.inner_apply, PiLp.single_apply, apply_ite]

def deDonderL2AdjointRow (row : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (test : SmoothScalarField period hPeriod) : DeDonderTensorL2 period hPeriod :=
  (frameTensorL2Space period hPeriod (finiteSmoothTangentFrame period hPeriod)).orthogonalProjectionOnto
    (deDonderRowAdjoint period hPeriod (finiteSmoothTangentFrame period hPeriod) metric reference row test)

theorem deDonderL2AdjointRow_pairing (field : DeDonderTensorL2 period hPeriod)
    (row : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : SmoothScalarField period hPeriod) :
    inner Real field (deDonderL2AdjointRow period hPeriod metric reference row test) =
      inner Real field.val (deDonderRowAdjoint period hPeriod (finiteSmoothTangentFrame period hPeriod) metric reference row test) :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left field _

theorem deDonderL2AdjointRow_mem_graph
    (row : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : SmoothScalarField period hPeriod) :
    (deDonderCovectorSingle period hPeriod row test, deDonderL2AdjointRow period hPeriod metric reference row test) ∈
      (deDonderL2Minimal period hPeriod metric).adjoint.graph := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (deDonderL2Minimal_denseDomain period hPeriod metric),
    Submodule.mem_adjoint_iff]
  intro field output hGraph
  apply sub_eq_zero.mpr
  rw [deDonderCovectorSingle_pairing, deDonderL2AdjointRow_pairing]
  exact deDonderL2_closedGraph_pairing period hPeriod metric reference (field, output)
    (by rw [← deDonderL2Minimal_graph period hPeriod metric reference]; exact hGraph) row test

include reference in
theorem deDonderCovectorSingle_mem_adjoint
    (row : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : SmoothScalarField period hPeriod) :
    deDonderCovectorSingle period hPeriod row test ∈ (deDonderL2Minimal period hPeriod metric).adjoint.domain := by
  obtain ⟨field, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (deDonderL2AdjointRow_mem_graph period hPeriod metric reference row test)
  change field.val = deDonderCovectorSingle period hPeriod row test at hInput
  rw [← hInput]
  exact field.property

theorem deDonderL2AdjointRow_action
    (row : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : SmoothScalarField period hPeriod) :
    (deDonderL2Minimal period hPeriod metric).adjoint
      ⟨deDonderCovectorSingle period hPeriod row test,
        deDonderCovectorSingle_mem_adjoint period hPeriod metric reference row test⟩ =
      deDonderL2AdjointRow period hPeriod metric reference row test := by
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp
    (deDonderL2AdjointRow_mem_graph period hPeriod metric reference row test)
  have hField : field = ⟨deDonderCovectorSingle period hPeriod row test,
      deDonderCovectorSingle_mem_adjoint period hPeriod metric reference row test⟩ := Subtype.ext hInput
  exact hField ▸ hOutput

end
end JanusFormal.P0EFTJanusProgramPT12DeDonderL2Adjoint4D