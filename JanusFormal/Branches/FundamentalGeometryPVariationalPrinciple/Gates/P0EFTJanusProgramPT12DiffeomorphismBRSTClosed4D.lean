import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismBRSTGraphRecovery4D

/-! Closability and minimal closed realization of the full actual diagonal BRST differential in L². -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismBRSTClosed4D
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

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

include reference in
theorem diffeomorphismBRST_closedGraph_vertical_zero
    (field : DiffeomorphismL2 period hPeriod (metric .plus))
    (hGraph : (0, field) ∈ (diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure) : field = 0 := by
  have hCartan := diffeomorphismBRST_closedGraph_cartan period hPeriod reference metric (0, field) hGraph
  have hInput : (diffeomorphismBRSTCartanReadout period hPeriod reference metric (0, field)).1 = 0 := by
    change regularGhostL2Recovery period hPeriod reference (metric .plus)
      (diffeomorphismTripletReadout period hPeriod (metric .plus) 0 0) = 0
    rw [map_zero, map_zero]
  have hOutput := (pairedCartanMinimal period hPeriod reference metric).graph_fst_eq_zero_snd hCartan hInput
  apply diffeomorphismL2_eq_zero_of_readouts period hPeriod (metric .plus) field
  · intro sector
    apply diffeomorphismTensorReadout_recovery_zero period hPeriod (metric .plus) reference sector field
    cases sector with
    | plus => exact congrArg (fun value : PairedCartanTensorL2 period hPeriod => WithLp.fst value) hOutput
    | minus => exact congrArg (fun value : PairedCartanTensorL2 period hPeriod => WithLp.snd value) hOutput
  · intro index
    simpa only [map_zero, ite_self] using diffeomorphismBRST_closedGraph_triplet period hPeriod metric index (0, field) hGraph

include reference in
theorem diffeomorphismL2BRST_isClosable : (diffeomorphismL2BRST period hPeriod metric).IsClosable := by
  refine ⟨(diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure.toLinearPMap, ?_⟩
  symm
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨x, y⟩ hPair hZero
  change x = 0 at hZero
  subst x
  exact diffeomorphismBRST_closedGraph_vertical_zero period hPeriod reference metric y hPair

def diffeomorphismL2BRSTMinimal :
    DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real] DiffeomorphismL2 period hPeriod (metric .plus) :=
  (diffeomorphismL2BRST period hPeriod metric).closure

include reference in
theorem diffeomorphismL2BRSTMinimal_isClosed : (diffeomorphismL2BRSTMinimal period hPeriod metric).IsClosed :=
  (diffeomorphismL2BRST_isClosable period hPeriod reference metric).closure_isClosed

include reference in
theorem diffeomorphismL2BRSTMinimal_graph : (diffeomorphismL2BRSTMinimal period hPeriod metric).graph =
    (diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure :=
  (diffeomorphismL2BRST_isClosable period hPeriod reference metric).graph_closure_eq_closure_graph.symm

theorem diffeomorphismL2BRSTMinimal_hasCore : (diffeomorphismL2BRSTMinimal period hPeriod metric).HasCore
    (diffeomorphismL2Smooth period hPeriod (metric .plus)).range :=
  (diffeomorphismL2BRST period hPeriod metric).closureHasCore

theorem diffeomorphismL2BRSTMinimal_denseDomain : Dense
    ((diffeomorphismL2BRSTMinimal period hPeriod metric).domain : Set (DiffeomorphismL2 period hPeriod (metric .plus))) :=
  (diffeomorphismL2BRST_denseDomain period hPeriod metric).mono (diffeomorphismL2BRST period hPeriod metric).le_closure.1

theorem diffeomorphismL2BRSTMinimal_smooth_mem
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismL2Smooth period hPeriod (metric .plus) field ∈
      (diffeomorphismL2BRSTMinimal period hPeriod metric).domain :=
  (diffeomorphismL2BRST period hPeriod metric).le_closure.1 ⟨field, rfl⟩

theorem diffeomorphismL2BRSTMinimal_smooth
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismL2BRSTMinimal period hPeriod metric
      ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) field,
        diffeomorphismL2BRSTMinimal_smooth_mem period hPeriod metric field⟩ =
      diffeomorphismL2Smooth period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismBRST period hPeriod metric field) :=
  ((diffeomorphismL2BRST period hPeriod metric).le_closure.2
    (x := ⟨_, ⟨field, rfl⟩⟩) (y := ⟨_, diffeomorphismL2BRSTMinimal_smooth_mem period hPeriod metric field⟩) rfl).symm.trans
      (diffeomorphismL2BRST_smooth period hPeriod metric field)

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismBRSTClosed4D

