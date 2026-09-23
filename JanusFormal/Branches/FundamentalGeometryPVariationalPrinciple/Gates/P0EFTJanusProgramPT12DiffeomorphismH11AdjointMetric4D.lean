import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11Adjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11Smooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InjectiveSmoothColumn4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11MetricDependence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedPhysical4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D

/-! The full diffeomorphism H11 column depends only on the physical metric perturbation. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12DiffeomorphismH11AdjointMetric4D
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

/-- The full H11 adjoint has only metric outputs. -/
theorem diffeomorphismH11Adjoint_graph_metric (input : CommonAugmentedHilbert period hPeriod configuration data analysis) (output : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))
    (hGraph : (input, output) ∈ (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph) :
    diffeomorphismMetricProjection period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) output = output := by
  have hTest := (diffeomorphismH11Adjoint_graph_iff period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input output).mp hGraph
  apply ext_inner_left Real
  intro test
  refine (diffeomorphismL2Smooth_denseRange period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)).induction_on test ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro field
    rw [← diffeomorphismMetricProjection_pairing, diffeomorphismMetricTransfer_L2,
      ← hTest, diffeomorphismH11Smooth_metricTransfer, hTest]

/-- It suffices to test the metric transfer, provided the output is metric. -/
theorem diffeomorphismH11Adjoint_graph_metric_iff (input : CommonAugmentedHilbert period hPeriod configuration data analysis) (output : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) :
    (input, output) ∈ (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph ↔
      diffeomorphismMetricProjection period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) output = output ∧
      ∀ field, inner Real (diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field) input =
        inner Real (diffeomorphismL2Smooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) (diffeomorphismMetricTransfer period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) field)) output := by
  constructor
  · intro hGraph
    refine ⟨diffeomorphismH11Adjoint_graph_metric period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input output hGraph, ?_⟩
    intro field
    rw [← diffeomorphismH11Smooth_metricTransfer period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field]
    exact (diffeomorphismH11Adjoint_graph_iff period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input output).mp hGraph _
  · rintro ⟨hMetric, hTest⟩
    apply (diffeomorphismH11Adjoint_graph_iff period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input output).mpr
    intro field
    rw [hTest, ← diffeomorphismMetricTransfer_L2, diffeomorphismMetricProjection_pairing, hMetric]

theorem diffeomorphismH11Adjoint_metric
    (input : (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).domain) :
    diffeomorphismMetricProjection period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input) =
      diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input :=
  diffeomorphismH11Adjoint_graph_metric period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input _
    ((diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).mem_graph input)

theorem diffeomorphismH11Adjoint_orthogonal_nonmetric
    (input : (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).domain) (test : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))
    (hTest : diffeomorphismMetricProjection period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) test = 0) :
    inner Real test (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input) = 0 := by
  calc
    _ = inner Real test (diffeomorphismMetricProjection period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input)) :=
      congrArg (inner Real test) (diffeomorphismH11Adjoint_metric period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input).symm
    _ = inner Real (diffeomorphismMetricProjection period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) test) (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input) :=
      (diffeomorphismMetricProjection_pairing period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) _ _).symm
    _ = 0 := by rw [hTest, inner_zero_left]

end
end
end P0EFTJanusProgramPT12DiffeomorphismH11AdjointMetric4D
end JanusFormal
