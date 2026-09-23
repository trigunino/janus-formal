import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11GraphBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszCore4D

/-! Completed matter and LL tests lie in the zero part of the full H11 adjoint. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12DiffeomorphismH11MatterLLTests4D
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
variable {measure : Measure (EffectiveQuotient period hPeriod)}
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
variable [IsFiniteMeasure measure]
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
  period hPeriod configuration.physical plusBase minusBase hBase)

variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis
  (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
  (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter))

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
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12InjectiveSmoothColumn4D

local instance physicalSourceInnerProductSpace : InnerProductSpace Real (DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2Ambient period hPeriod)
    (diffeomorphismL2Space period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))

open P0EFTJanusProgramPT12DiffeomorphismH11Core4D

attribute [local irreducible] diffeomorphismH11Smooth diffeomorphismH11Core

open P0EFTJanusProgramPT12DiffeomorphismH11Adjoint4D
open P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D

open P0EFTJanusProgramPT12DiffeomorphismH11AdjointMetric4D

local instance physicalMetricInnerProductSpace : InnerProductSpace Real (DiffeomorphismMetricL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real)
    (E := DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) (diffeomorphismMetricProjection period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)).range

open P0EFTJanusProgramPT12DiffeomorphismGraphToL24D
open P0EFTJanusProgramPT12DiffeomorphismH11MetricBound4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
attribute [local instance]
  globalDiffeomorphismOffShellGraphNormedSpace globalDiffeomorphismOffShellGraphModule
  globalDiffeomorphismOffShellGraphInnerProductSpace globalDiffeomorphismOffShellGraphCompleteSpace
  diagonalGraphNormedSpace diagonalGraphModule diagonalGraphInnerProductSpace diagonalGraphCompleteSpace
attribute [local irreducible] diffeomorphismGraphToL2

open P0EFTJanusProgramPT12DiffeomorphismH11GraphBridge4D
open P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszZero4D

/-- The completed matter/LL test column vanishes in the original graph. -/
theorem diffeomorphismH11GraphTranspose_completedMatterLL_zero (state : ProgramPT12StrongCompletedMatterLL period hPeriod configuration data analysis) :
    diffeomorphismH11GraphTranspose period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical ((programPT12StrongCompletedMatterLLInclusion (configuration := configuration) (data := data) (analysis := analysis) period hPeriod) state) = 0 := by
  have hZero : strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical ((programPT12StrongCompletedMatterLLInclusion (configuration := configuration) (data := data) (analysis := analysis) period hPeriod) state) = 0 :=
    strongPhysicalRiesz_completedMatterLL_zero period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical state
  change actualDiffeomorphismReadout period hPeriod configuration data analysis
    (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical ((programPT12StrongCompletedMatterLLInclusion (configuration := configuration) (data := data) (analysis := analysis) period hPeriod) state)) = 0
  rw [hZero, map_zero]

theorem diffeomorphismH11Adjoint_completedMatterLL_graph (state : ProgramPT12StrongCompletedMatterLL period hPeriod configuration data analysis) :
    ((programPT12StrongCompletedMatterLLInclusion (configuration := configuration) (data := data) (analysis := analysis) period hPeriod) state, 0) ∈ (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph :=
  (diffeomorphismH11Adjoint_zero_graph_iff period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical _).mpr
    (diffeomorphismH11GraphTranspose_completedMatterLL_zero period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical state)

/-- These completed tests require no additional L2 estimate. -/
theorem diffeomorphismH11Adjoint_completedMatterLL_mem_domain (state : ProgramPT12StrongCompletedMatterLL period hPeriod configuration data analysis) :
    (programPT12StrongCompletedMatterLLInclusion (configuration := configuration) (data := data) (analysis := analysis) period hPeriod) state ∈ (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).domain := by
  rw [diffeomorphismH11Adjoint_domain_iff_graphRange,
    diffeomorphismH11GraphTranspose_completedMatterLL_zero]
  exact ⟨0, map_zero _⟩

theorem diffeomorphismH11MetricBound_completedMatterLL (state : ProgramPT12StrongCompletedMatterLL period hPeriod configuration data analysis) :
    diffeomorphismH11MetricTestBound period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical ((programPT12StrongCompletedMatterLLInclusion (configuration := configuration) (data := data) (analysis := analysis) period hPeriod) state) :=
  (diffeomorphismH11Adjoint_domain_iff_metricBound period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical _).mp
    (diffeomorphismH11Adjoint_completedMatterLL_mem_domain period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical state)

attribute [local irreducible] diffeomorphismH11GraphTranspose

theorem diffeomorphismH11GraphTranspose_add_completedMatterLL
    (input : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (state : ProgramPT12StrongCompletedMatterLL period hPeriod configuration data analysis) :
    diffeomorphismH11GraphTranspose period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical (input + (programPT12StrongCompletedMatterLLInclusion (configuration := configuration) (data := data) (analysis := analysis) period hPeriod) state) = diffeomorphismH11GraphTranspose period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input :=
  (map_add (diffeomorphismH11GraphTranspose period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) input ((programPT12StrongCompletedMatterLLInclusion (configuration := configuration) (data := data) (analysis := analysis) period hPeriod) state)).trans
    ((congrArg (fun value => diffeomorphismH11GraphTranspose period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input + value)
      (diffeomorphismH11GraphTranspose_completedMatterLL_zero period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical state)).trans (add_zero _))
/-- Adding any completed matter/LL tail leaves the entire adjoint graph unchanged. -/
theorem diffeomorphismH11Adjoint_graph_add_completedMatterLL_iff
    (input : CommonAugmentedHilbert period hPeriod configuration data analysis) (output : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) (state : ProgramPT12StrongCompletedMatterLL period hPeriod configuration data analysis) :
    (input + (programPT12StrongCompletedMatterLLInclusion (configuration := configuration) (data := data) (analysis := analysis) period hPeriod) state, output) ∈ (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph ↔
      (input, output) ∈ (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph := by
  rw [diffeomorphismH11Adjoint_graph_iff_graphTranspose,
    diffeomorphismH11Adjoint_graph_iff_graphTranspose]
  exact (congrArg (fun value =>
    (diffeomorphismGraphToL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data)).adjoint output = value)
    (diffeomorphismH11GraphTranspose_add_completedMatterLL period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input state)).to_iff

theorem diffeomorphismH11MetricBound_add_completedMatterLL_iff
    (input : CommonAugmentedHilbert period hPeriod configuration data analysis) (state : ProgramPT12StrongCompletedMatterLL period hPeriod configuration data analysis) :
    diffeomorphismH11MetricTestBound period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical (input + (programPT12StrongCompletedMatterLLInclusion (configuration := configuration) (data := data) (analysis := analysis) period hPeriod) state) ↔
      diffeomorphismH11MetricTestBound period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input := by
  rw [diffeomorphismH11MetricBound_iff_graphRange, diffeomorphismH11MetricBound_iff_graphRange]
  exact (congrArg (fun value => value ∈
    (diffeomorphismGraphToL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data)).adjoint.range)
    (diffeomorphismH11GraphTranspose_add_completedMatterLL period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input state)).to_iff

end
end
end P0EFTJanusProgramPT12DiffeomorphismH11MatterLLTests4D
end JanusFormal
