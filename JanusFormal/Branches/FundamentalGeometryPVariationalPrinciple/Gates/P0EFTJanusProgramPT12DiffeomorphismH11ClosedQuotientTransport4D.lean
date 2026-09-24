import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11QuotientMinimal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11Minimal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11QuotientDuality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11AdjointDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DenseAdjointMinimalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11MetricTests4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11MatterLLTests4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11MetricPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongInteractionBRSTL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11AbelianTests4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongEinsteinMaxwellBRSTL24D
namespace JanusFormal
namespace P0EFTJanusProgramPT12DiffeomorphismH11ClosedQuotientTransport4D
set_option autoImplicit false

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalEuler4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12StrongLLPhysicalMixedHessianZero4D
open P0EFTJanusProgramPT12StrongMatterLLSameActionBridge4D
open P0EFTJanusProgramPT12StrongPhysicalSecondJet4D
open P0EFTJanusProgramPT12StrongToH11PhysicalSecondJet4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterCompleteSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLCompleteSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
  P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D.programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)

set_option backward.isDefEq.respectTransparency false
open P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszZero4D
open P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D
open P0EFTJanusProgramPT12LLQuotientFriedrichsSmoothPairing4D
open P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D

open P0EFTJanusProgramPT12StrongFullLLQuotientColumn4D
open P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxKernel4D
open P0EFTJanusProgramPT12DiagonalGhostHilbertQuotient4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

open P0EFTJanusProgramPT12StrongGhostLLNullSpace4D
open P0EFTJanusProgramPT12ClosedNullQuotient4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D

open P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D
open P0EFTJanusProgramPT12JointQuotientAbelianFactor4D
open P0EFTJanusProgramPT12SignedBRSTAugmentedPairing4D
open P0EFTJanusProgramPT12AbelianSignedBRSTRealization4D
open P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
  period hPeriod configuration.physical plusBase minusBase hBase)

variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis
  (strongChart (measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod) period hPeriod configuration data analysis realization plusBase minusBase hBase)
  (strongBridge (measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter))

open P0EFTJanusProgramPT12JointQuotientAbelianColumn4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

open P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
open P0EFTJanusProgramPT12AbelianLorenzGraphShear4D
open P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D
open P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D

open P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D

open P0EFTJanusProgramPT12CandidateAAbelianMixedOperator4D
open P0EFTJanusProgramPT12CandidateAAbelianMixedPotential4D
open P0EFTJanusProgramPT12AbelianPotentialGraphInclusion4D
open P0EFTJanusProgramPT12AbelianGhostRotationPhysical4D

open P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D
open P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D

open P0EFTJanusProgramPT12DiffeomorphismH11MetricDependence4D

open P0EFTJanusProgramPT12DiffeomorphismH11Smooth4D
open P0EFTJanusProgramPT12DiffeomorphismH11MetricBound4D
open P0EFTJanusProgramPT12DiffeomorphismH11Adjoint4D
open P0EFTJanusProgramPT12StrongPhysicalBRSTMixedHessian4D
open P0EFTJanusProgramPT12StrongMaxwellBRSTMixedL24D

open P0EFTJanusProgramPT12StrongPhysicalBRSTMetricHessian4D
open P0EFTJanusProgramPT12StrongEinsteinMaxwellBRSTL24D
open P0EFTJanusProgramPT12StrongEinsteinBRSTL24D
open P0EFTJanusProgramPT12StrongMaxwellBRSTL24D

open P0EFTJanusProgramPT12DiffeomorphismL2Core4D

open P0EFTJanusProgramPT12DiffeomorphismH11MetricPairing4D
open P0EFTJanusProgramPT12StrongInteractionBRSTL24D

open P0EFTJanusProgramPT12DiffeomorphismH11MetricTests4D
open P0EFTJanusProgramPT12DiffeomorphismH11AbelianTests4D
open P0EFTJanusProgramPT12DiffeomorphismH11MatterLLTests4D

open P0EFTJanusProgramPT12DiffeomorphismH11AdjointDensity4D
open P0EFTJanusProgramPT12DiffeomorphismH11Core4D
open P0EFTJanusProgramPT12DenseAdjointMinimalClosure4D

local instance physicalSourceInnerProductSpace : InnerProductSpace Real
    (DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2Ambient period hPeriod)
    (diffeomorphismL2Space period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))

open P0EFTJanusProgramPT12StrongGhostLLNullSpace4D
open P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D
open P0EFTJanusProgramPT12DiffeomorphismH11QuotientAdjoint4D
open P0EFTJanusProgramPT12DiffeomorphismH11QuotientCore4D
open P0EFTJanusProgramPT12DiffeomorphismH11QuotientDuality4D
open P0EFTJanusProgramPT12InjectiveSmoothColumn4D

open P0EFTJanusProgramPT12DiffeomorphismH11Minimal4D
open P0EFTJanusProgramPT12DiffeomorphismH11QuotientMinimal4D
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

private theorem closure_range_map
    {D E F G : Type*} [AddCommGroup D] [Module Real D]
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (inclusion : D →ₗ[Real] E) (source : D →ₗ[Real] F) (target : D →ₗ[Real] G)
    (map : F →L[Real] G) (hMap : ∀ field, map (source field) = target field)
    (pair : E × F) (hPair : pair ∈ (inclusion.prod source).range.topologicalClosure) :
    (pair.1, map pair.2) ∈ (inclusion.prod target).range.topologicalClosure := by
  have hClosed : IsClosed {pair : E × F | (pair.1, map pair.2) ∈ (inclusion.prod target).range.topologicalClosure} :=
    (inclusion.prod target).range.isClosed_topologicalClosure.preimage
      (continuous_fst.prodMk (map.continuous.comp continuous_snd))
  apply closure_minimal _ hClosed hPair
  rintro _ ⟨field, rfl⟩
  apply (inclusion.prod target).range.le_topologicalClosure
  exact ⟨field, Prod.ext rfl (hMap field).symm⟩

theorem diffeomorphismH11Minimal_graph_project
    (input : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))
    (output : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hGraph : (input, output) ∈ (diffeomorphismH11Minimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph) :
    (input, (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ output) ∈
      (diffeomorphismH11QuotientMinimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph := by
  rw [diffeomorphismH11Minimal_graph] at hGraph
  rw [diffeomorphismH11QuotientMinimal_graph]
  exact closure_range_map _ _ _ (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQL
    (fun _ => rfl) (input, output) hGraph

theorem diffeomorphismH11QuotientMinimal_graph_lift
    (input : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))
    (output : JointGhostLLQuotient period hPeriod configuration data analysis)
    (hGraph : (input, output) ∈ (diffeomorphismH11QuotientMinimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph) :
    (input, quotientLift (jointGhostLLNullSpace period hPeriod configuration data analysis) output) ∈
      (diffeomorphismH11Minimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph := by
  rw [diffeomorphismH11QuotientMinimal_graph] at hGraph
  rw [diffeomorphismH11Minimal_graph]
  apply closure_range_map _ _ _ (quotientLift (jointGhostLLNullSpace period hPeriod configuration data analysis)) _ (input, output) hGraph
  intro field
  exact quotientLift_mk _ _
    (diffeomorphismH11Smooth_jointNull_orthogonal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field)

theorem diffeomorphismH11QuotientMinimal_graph_iff_lift
    (input : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))
    (output : JointGhostLLQuotient period hPeriod configuration data analysis) :
    (input, output) ∈ (diffeomorphismH11QuotientMinimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph ↔
    (input, quotientLift (jointGhostLLNullSpace period hPeriod configuration data analysis) output) ∈
      (diffeomorphismH11Minimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph := by
  constructor
  · exact diffeomorphismH11QuotientMinimal_graph_lift period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input output
  · intro hGraph
    have h := diffeomorphismH11Minimal_graph_project period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical _ _ hGraph
    rwa [mk_quotientLift] at h

theorem diffeomorphismH11QuotientMinimal_domain_eq :
    (diffeomorphismH11QuotientMinimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).domain =
    (diffeomorphismH11Minimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).domain := by
  ext input
  constructor
  · intro hInput
    exact LinearPMap.mem_domain_of_mem_graph
      (diffeomorphismH11QuotientMinimal_graph_lift period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical _ _
        ((diffeomorphismH11QuotientMinimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).mem_graph ⟨input, hInput⟩))
  · intro hInput
    exact LinearPMap.mem_domain_of_mem_graph
      (diffeomorphismH11Minimal_graph_project period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical _ _
        ((diffeomorphismH11Minimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).mem_graph ⟨input, hInput⟩))

theorem diffeomorphismH11Minimal_output_orthogonal
    (input : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))
    (output : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hGraph : (input, output) ∈ (diffeomorphismH11Minimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph) :
    output ∈ (jointGhostLLNullSpace period hPeriod configuration data analysis)ᗮ := by
  have hBack := diffeomorphismH11QuotientMinimal_graph_lift period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical _ _
    (diffeomorphismH11Minimal_graph_project period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input output hGraph)
  have hEqual := (diffeomorphismH11Minimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).mem_graph_snd_inj hBack hGraph rfl
  rw [← hEqual]
  exact ((jointGhostLLNullSpace period hPeriod configuration data analysis).quotientEquivOrthogonal
    ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ output)).property

theorem diffeomorphismH11Minimal_quotient_output_norm
    (input : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))
    (output : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hGraph : (input, output) ∈ (diffeomorphismH11Minimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph) :
    ‖(jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ output‖ = ‖output‖ := by
  have hLift := quotientLift_mk (jointGhostLLNullSpace period hPeriod configuration data analysis) output
    (diffeomorphismH11Minimal_output_orthogonal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input output hGraph)
  have hNorm : ‖quotientLift (jointGhostLLNullSpace period hPeriod configuration data analysis)
      ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ output)‖ =
      ‖(jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ output‖ :=
    (jointGhostLLNullSpace period hPeriod configuration data analysis).quotientEquivOrthogonal.norm_map _
  exact hNorm.symm.trans (congrArg norm hLift)

theorem diffeomorphismH11Minimal_quotient_pairing
    (input : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))
    (output test : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hGraph : (input, output) ∈ (diffeomorphismH11Minimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph) :
    inner Real ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ output)
      ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ test) = inner Real output test :=
  P0EFTJanusProgramPT12ClosedNullQuotient4D.inner_mk_of_left_orthogonal _ _ _
    (diffeomorphismH11Minimal_output_orthogonal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input output hGraph)

theorem diffeomorphismH11QuotientMinimal_zero_graph_iff
    (input : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) :
    (input, 0) ∈ (diffeomorphismH11QuotientMinimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph ↔
    (input, 0) ∈ (diffeomorphismH11Minimal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph := by
  rw [diffeomorphismH11QuotientMinimal_graph_iff_lift, map_zero]

end
end
end P0EFTJanusProgramPT12DiffeomorphismH11ClosedQuotientTransport4D
end JanusFormal
