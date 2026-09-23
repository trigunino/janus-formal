import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismBRSTClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismDoubletGraphClosure4D

/-! Nilpotency and the explicit nonminimal doublet contraction on the closed actual BRST domain. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismBRSTClosedComplex4D
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
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12PairedRegularFrameCartan4D
open P0EFTJanusProgramPT12PairedRegularFrameCartanCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

open P0EFTJanusProgramPT12RegularTensorL2Bridge4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2BRST4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

open P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
open P0EFTJanusProgramPT12RegularGhostL2Recovery4D

open P0EFTJanusProgramPT12DiffeomorphismBRSTGraphRecovery4D

open P0EFTJanusProgramPT12DiffeomorphismBRSTClosed4D
open P0EFTJanusProgramPT12DiffeomorphismL2Doublet4D
open P0EFTJanusProgramPT12DiffeomorphismDoubletGraphClosure4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

theorem diffeomorphismBRST_closedGraph_step
    (pair : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus))
    (hPair : pair ∈ (diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure) :
    (pair.2, 0) ∈ (diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure := by
  let H := DiffeomorphismL2 period hPeriod (metric .plus)
  let q := diffeomorphismL2BRST period hPeriod metric
  let step : (H × H) →L[Real] (H × H) := (ContinuousLinearMap.snd Real H H).prod 0
  have hMaps : Set.MapsTo step (q.graph : Set (H × H)) (q.graph : Set (H × H)) := by
    intro value hValue
    obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
    apply (LinearPMap.mem_graph_iff _).mpr
    exact ⟨⟨q field, diffeomorphismL2BRST_apply_mem period hPeriod metric field⟩,
      hOutput, diffeomorphismL2BRST_square_zero period hPeriod metric field⟩
  exact hMaps.closure step.continuous hPair

include reference in
theorem diffeomorphismL2BRSTMinimal_step_graph
    (field : (diffeomorphismL2BRSTMinimal period hPeriod metric).domain) :
    (diffeomorphismL2BRSTMinimal period hPeriod metric field, 0) ∈
      (diffeomorphismL2BRSTMinimal period hPeriod metric).graph := by
  have hGraph : (field.val, diffeomorphismL2BRSTMinimal period hPeriod metric field) ∈
      (diffeomorphismL2BRSTMinimal period hPeriod metric).graph :=
    (LinearPMap.mem_graph_iff _).mpr ⟨field, rfl, rfl⟩
  rw [diffeomorphismL2BRSTMinimal_graph period hPeriod reference metric] at hGraph ⊢
  exact diffeomorphismBRST_closedGraph_step period hPeriod metric _ hGraph

include reference in
theorem diffeomorphismL2BRSTMinimal_apply_mem
    (field : (diffeomorphismL2BRSTMinimal period hPeriod metric).domain) :
    diffeomorphismL2BRSTMinimal period hPeriod metric field ∈
      (diffeomorphismL2BRSTMinimal period hPeriod metric).domain := by
  obtain ⟨value, hValue, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (diffeomorphismL2BRSTMinimal_step_graph period hPeriod reference metric field)
  exact (congrArg (fun x : DiffeomorphismL2 period hPeriod (metric .plus) =>
    x ∈ (diffeomorphismL2BRSTMinimal period hPeriod metric).domain) hValue).mp value.property

theorem diffeomorphismL2BRSTMinimal_square_zero
    (field : (diffeomorphismL2BRSTMinimal period hPeriod metric).domain) :
    diffeomorphismL2BRSTMinimal period hPeriod metric
      ⟨diffeomorphismL2BRSTMinimal period hPeriod metric field,
        diffeomorphismL2BRSTMinimal_apply_mem period hPeriod reference metric field⟩ = 0 := by
  obtain ⟨value, hValue, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp
    (diffeomorphismL2BRSTMinimal_step_graph period hPeriod reference metric field)
  exact (congrArg (diffeomorphismL2BRSTMinimal period hPeriod metric) (Subtype.ext hValue.symm)).trans hOutput

include reference in
theorem diffeomorphismL2BRSTMinimal_contract_graph
    (field : (diffeomorphismL2BRSTMinimal period hPeriod metric).domain) :
    (diffeomorphismL2Homotopy period hPeriod metric field.val,
      diffeomorphismL2DoubletProjection period hPeriod metric field.val -
        diffeomorphismL2Homotopy period hPeriod metric (diffeomorphismL2BRSTMinimal period hPeriod metric field)) ∈
      (diffeomorphismL2BRSTMinimal period hPeriod metric).graph := by
  have hGraph : (field.val, diffeomorphismL2BRSTMinimal period hPeriod metric field) ∈
      (diffeomorphismL2BRSTMinimal period hPeriod metric).graph :=
    (LinearPMap.mem_graph_iff _).mpr ⟨field, rfl, rfl⟩
  rw [diffeomorphismL2BRSTMinimal_graph period hPeriod reference metric] at hGraph ⊢
  exact diffeomorphismL2BRST_closedGraph_contract period hPeriod metric _ _ hGraph

include reference in
theorem diffeomorphismL2BRSTMinimal_homotopy_mem
    (field : (diffeomorphismL2BRSTMinimal period hPeriod metric).domain) :
    diffeomorphismL2Homotopy period hPeriod metric field.val ∈
      (diffeomorphismL2BRSTMinimal period hPeriod metric).domain := by
  obtain ⟨value, hValue, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (diffeomorphismL2BRSTMinimal_contract_graph period hPeriod reference metric field)
  exact (congrArg (fun x : DiffeomorphismL2 period hPeriod (metric .plus) =>
    x ∈ (diffeomorphismL2BRSTMinimal period hPeriod metric).domain) hValue).mp value.property

theorem diffeomorphismL2BRSTMinimal_contract
    (field : (diffeomorphismL2BRSTMinimal period hPeriod metric).domain) :
    diffeomorphismL2BRSTMinimal period hPeriod metric
      ⟨diffeomorphismL2Homotopy period hPeriod metric field.val,
        diffeomorphismL2BRSTMinimal_homotopy_mem period hPeriod reference metric field⟩ +
      diffeomorphismL2Homotopy period hPeriod metric (diffeomorphismL2BRSTMinimal period hPeriod metric field) =
        diffeomorphismL2DoubletProjection period hPeriod metric field.val := by
  obtain ⟨value, hValue, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp
    (diffeomorphismL2BRSTMinimal_contract_graph period hPeriod reference metric field)
  apply eq_sub_iff_add_eq.mp
  exact (congrArg (diffeomorphismL2BRSTMinimal period hPeriod metric) (Subtype.ext hValue.symm)).trans hOutput

theorem diffeomorphismL2BRSTMinimal_doublet_cycle_exact
    (field : (diffeomorphismL2BRSTMinimal period hPeriod metric).domain)
    (hCycle : diffeomorphismL2BRSTMinimal period hPeriod metric field = 0) :
    diffeomorphismL2BRSTMinimal period hPeriod metric
      ⟨diffeomorphismL2Homotopy period hPeriod metric field.val,
        diffeomorphismL2BRSTMinimal_homotopy_mem period hPeriod reference metric field⟩ =
      diffeomorphismL2DoubletProjection period hPeriod metric field.val := by
  have h := diffeomorphismL2BRSTMinimal_contract period hPeriod reference metric field
  rw [hCycle, map_zero, add_zero] at h
  exact h

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismBRSTClosedComplex4D

