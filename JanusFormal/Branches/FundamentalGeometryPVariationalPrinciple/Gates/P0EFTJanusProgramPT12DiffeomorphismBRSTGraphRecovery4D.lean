import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Recovery4D

/-! The closure of the actual BRST graph retains the paired Cartan and nonminimal equations. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismBRSTGraphRecovery4D
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

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

private def recoveredMetricPair : DiffeomorphismL2 period hPeriod (metric .plus) →L[Real] PairedCartanTensorL2 period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real _ _).symm.toContinuousLinearMap.comp
    (((regularTensorL2Recovery period hPeriod reference).comp
      (diffeomorphismTensorReadout period hPeriod (metric .plus) .plus)).prod
     ((regularTensorL2Recovery period hPeriod reference).comp
      (diffeomorphismTensorReadout period hPeriod (metric .plus) .minus)))

def diffeomorphismBRSTCartanReadout :
    (DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus)) →L[Real]
      (CartanGhostL2 period hPeriod × PairedCartanTensorL2 period hPeriod) :=
  (((regularGhostL2Recovery period hPeriod reference (metric .plus)).comp
    (diffeomorphismTripletReadout period hPeriod (metric .plus) 0)).comp (ContinuousLinearMap.fst Real _ _)).prod
    ((recoveredMetricPair period hPeriod reference metric).comp (ContinuousLinearMap.snd Real _ _))

theorem diffeomorphismBRSTCartanReadout_smooth
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismBRSTCartanReadout period hPeriod reference metric
      (diffeomorphismL2Smooth period hPeriod (metric .plus) field,
       diffeomorphismL2Smooth period hPeriod (metric .plus)
         (globalCandidateADiagonalDiffeomorphismBRST period hPeriod metric field)) =
      (regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference field.nonminimal.ghost.field),
       pairedRegularFrameCartanSmoothOutput period hPeriod reference metric
         (regularFrameCartanGhostCoefficient period hPeriod reference field.nonminimal.ghost.field)) := by
  apply Prod.ext
  · exact regularGhostL2Recovery_actual period hPeriod reference (metric .plus) field.nonminimal.ghost.field
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change regularTensorL2Recovery period hPeriod reference
        (globalGeneralMetricTensorFrameL2LinearMap period hPeriod
          (smoothMetricCartanAction period hPeriod field.nonminimal.ghost.field (metric .plus).tensor)) =
          regularFrameCartanL2 period hPeriod reference (metric .plus).tensor
            (regularFrameCartanGhostCoefficient period hPeriod reference field.nonminimal.ghost.field)
      rw [regularTensorL2Recovery_smooth, regularFrameCartanL2_eq_tensorL2,
        regularFrameGhostFromCoefficients_reconstructs]
    · change regularTensorL2Recovery period hPeriod reference
        (globalGeneralMetricTensorFrameL2LinearMap period hPeriod
          (smoothMetricCartanAction period hPeriod field.nonminimal.ghost.field (metric .minus).tensor)) =
          regularFrameCartanL2 period hPeriod reference (metric .minus).tensor
            (regularFrameCartanGhostCoefficient period hPeriod reference field.nonminimal.ghost.field)
      rw [regularTensorL2Recovery_smooth, regularFrameCartanL2_eq_tensorL2,
        regularFrameGhostFromCoefficients_reconstructs]

theorem diffeomorphismBRST_graph_smooth_rep
    (pair : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus))
    (hPair : pair ∈ (diffeomorphismL2BRST period hPeriod metric).graph) :
    ∃ field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod,
      pair = (diffeomorphismL2Smooth period hPeriod (metric .plus) field,
        diffeomorphismL2Smooth period hPeriod (metric .plus)
          (globalCandidateADiagonalDiffeomorphismBRST period hPeriod metric field)) := by
  obtain ⟨value, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hPair
  obtain ⟨field, hField⟩ := value.property
  have hAction : diffeomorphismL2BRST period hPeriod metric value =
      diffeomorphismL2Smooth period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismBRST period hPeriod metric field) :=
    (congrArg (diffeomorphismL2BRST period hPeriod metric) (Subtype.ext hField.symm)).trans
      (diffeomorphismL2BRST_smooth period hPeriod metric field)
  exact ⟨field, Prod.ext (hField.trans hInput).symm (hOutput.symm.trans hAction)⟩

theorem diffeomorphismBRST_closedGraph_cartan
    (pair : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus))
    (hPair : pair ∈ (diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure) :
    diffeomorphismBRSTCartanReadout period hPeriod reference metric pair ∈
      (pairedCartanMinimal period hPeriod reference metric).graph := by
  have hClosed := (pairedCartanMinimal_isClosed period hPeriod reference metric).preimage
    (diffeomorphismBRSTCartanReadout period hPeriod reference metric).continuous
  apply (closure_minimal _ hClosed) hPair
  intro value hValue
  obtain ⟨field, rfl⟩ := diffeomorphismBRST_graph_smooth_rep period hPeriod metric value hValue
  change diffeomorphismBRSTCartanReadout period hPeriod reference metric _ ∈
    (pairedCartanMinimal period hPeriod reference metric).graph
  rw [diffeomorphismBRSTCartanReadout_smooth]
  exact pairedCartanMinimal_smooth_graph period hPeriod reference metric _

theorem diffeomorphismBRST_triplet_smooth (index : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletReadout period hPeriod (metric .plus) index
      (diffeomorphismL2Smooth period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismBRST period hPeriod metric field)) =
      if index = 1 then diffeomorphismTripletReadout period hPeriod (metric .plus) 2
        (diffeomorphismL2Smooth period hPeriod (metric .plus) field) else 0 := by
  fin_cases index
  · exact (globalNormalizedVectorFrameL2LinearMap period hPeriod (metric .plus)).map_zero
  · rfl
  · exact (globalNormalizedVectorFrameL2LinearMap period hPeriod (metric .plus)).map_zero

theorem diffeomorphismBRST_closedGraph_triplet (index : Fin 3)
    (pair : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus))
    (hPair : pair ∈ (diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure) :
    diffeomorphismTripletReadout period hPeriod (metric .plus) index pair.2 =
      if index = 1 then diffeomorphismTripletReadout period hPeriod (metric .plus) 2 pair.1 else 0 := by
  have hClosed : IsClosed {value : DiffeomorphismL2 period hPeriod (metric .plus) ×
      DiffeomorphismL2 period hPeriod (metric .plus) |
      diffeomorphismTripletReadout period hPeriod (metric .plus) index value.2 =
        if index = 1 then diffeomorphismTripletReadout period hPeriod (metric .plus) 2 value.1 else 0} := by
    apply isClosed_eq
    · exact (diffeomorphismTripletReadout period hPeriod (metric .plus) index).continuous.comp continuous_snd
    · split_ifs
      · exact (diffeomorphismTripletReadout period hPeriod (metric .plus) 2).continuous.comp continuous_fst
      · exact continuous_const
  apply (closure_minimal _ hClosed) hPair
  intro value hValue
  obtain ⟨field, rfl⟩ := diffeomorphismBRST_graph_smooth_rep period hPeriod metric value hValue
  exact diffeomorphismBRST_triplet_smooth period hPeriod metric index field

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismBRSTGraphRecovery4D
