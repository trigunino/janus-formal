import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11AdjointMetric4D

/-! Constructing the full H11 adjoint from a metric smooth-test estimate. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12DiffeomorphismH11MetricBound4D
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

/-- A scalar test against the entire physical output, not merely its metric block. -/
def diffeomorphismH11MetricTest (input : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real] Real :=
  (innerₛₗ Real input).comp (diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)

def diffeomorphismH11MetricTestBound (input : CommonAugmentedHilbert period hPeriod configuration data analysis) : Prop :=
  ∃ bound : Real, ∀ field,
    ‖diffeomorphismH11MetricTest period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input field‖ ≤
      bound * ‖diffeomorphismMetricSmooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) field‖

/-- The metric Riesz representative furnished by the smooth test estimate. -/
def diffeomorphismH11MetricRiesz (input : CommonAugmentedHilbert period hPeriod configuration data analysis) : DiffeomorphismMetricL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) :=
  (InnerProductSpace.toDual Real (DiffeomorphismMetricL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))).symm
    ((diffeomorphismH11MetricTest period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input).extendOfNorm (diffeomorphismMetricSmooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)))

theorem diffeomorphismH11MetricRiesz_pairing (input : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hBound : diffeomorphismH11MetricTestBound period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (diffeomorphismH11MetricRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input) (diffeomorphismMetricSmooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) field) =
      inner Real input (diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field) := by
  unfold diffeomorphismH11MetricRiesz
  rw [InnerProductSpace.toDual_symm_apply,
    LinearMap.extendOfNorm_eq (diffeomorphismMetricSmooth_denseRange period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) hBound]
  rfl

theorem diffeomorphismH11MetricRiesz_graph (input : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hBound : diffeomorphismH11MetricTestBound period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input) :
    (input, (diffeomorphismH11MetricRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input).val) ∈
      (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).graph := by
  apply (diffeomorphismH11Adjoint_graph_iff period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input _).mpr
  intro field
  calc
    inner Real (diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field) input =
        inner Real (diffeomorphismMetricSmooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) field) (diffeomorphismH11MetricRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input) := by
      rw [← real_inner_comm (diffeomorphismMetricSmooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) field),
        diffeomorphismH11MetricRiesz_pairing period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input hBound, real_inner_comm]
    _ = inner Real (diffeomorphismMetricProjection period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) (diffeomorphismL2Smooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) field))
        (diffeomorphismH11MetricRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input).val := rfl
    _ = inner Real (diffeomorphismL2Smooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) field) (diffeomorphismH11MetricRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input).val := by
      rw [diffeomorphismMetricProjection_pairing, diffeomorphismMetric_fixed]

/-- Exact analytic criterion for the adjoint domain, using only metric L2 norms. -/
theorem diffeomorphismH11Adjoint_domain_iff_metricBound (input : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    input ∈ (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).domain ↔
      diffeomorphismH11MetricTestBound period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input := by
  constructor
  · intro hInput
    let value := (diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) ⟨input, hInput⟩
    have hPair := ((diffeomorphismH11Adjoint_graph_metric_iff period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input value).mp
      ((diffeomorphismH11Adjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).mem_graph ⟨input, hInput⟩)).2
    refine ⟨‖value‖, ?_⟩
    intro field
    change ‖inner Real input (diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field)‖ ≤ _
    rw [← real_inner_comm input, hPair]
    change _ ≤ ‖value‖ * ‖(diffeomorphismMetricSmooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) field).val‖
    rw [diffeomorphismMetricSmooth_original, mul_comm]
    exact norm_inner_le_norm _ _
  · intro hBound
    obtain ⟨value, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
      (diffeomorphismH11MetricRiesz_graph period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical input hBound)
    change (value : CommonAugmentedHilbert period hPeriod configuration data analysis) = input at hInput
    rw [← hInput]
    exact value.property

end
end
end P0EFTJanusProgramPT12DiffeomorphismH11MetricBound4D
end JanusFormal
