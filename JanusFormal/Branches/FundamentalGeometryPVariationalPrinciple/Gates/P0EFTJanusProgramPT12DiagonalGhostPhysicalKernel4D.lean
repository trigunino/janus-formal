import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalGhostCancellation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PureNonminimalSevenPhysicalNull4D

/-! The shared-ghost cancellation persists in the full H11-augmented actual operator. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalGhostPhysicalKernel4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000
set_option maxRecDepth 4000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPT12DiagonalGhostCancellation4D

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod configuration.physical
  couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)

open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
set_option backward.isDefEq.respectTransparency false

/-- Pure shared ghost inside the complete actual smooth core. -/
def diagonalPureGhostCore
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  (diagonalPureGhost period hPeriod ghost, 0)

theorem diagonalPureGhostCore_physicalTangent_zero
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis
      (diagonalPureGhostCore period hPeriod configuration analysis ghost) = 0 := by
  exact diagonalExtendedBulkMinimalPhysicalTangent_pureDiffeomorphismNonminimal_eq_zero
    period hPeriod configuration data analysis
    (diagonalPureGhost period hPeriod ghost).nonminimal

variable (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
  NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)

theorem diagonalPureGhostCore_physicalHessian_left_zero
    (ghost : GlobalDiffeomorphismGhostField period hPeriod)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
      configuration data analysis chart sameAction.chartBridge
      (diagonalPureGhostCore period hPeriod configuration analysis ghost) test = 0 := by
  unfold diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
  rw [diagonalPureGhostCore_physicalTangent_zero]
  simp

variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
  hPeriod configuration data analysis chart sameAction)

theorem diagonalPureGhostCore_augmented_pairing_zero
    (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
      globalCandidateAMetricBySector period hPeriod data .minus)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings = 0)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    globalCandidateACommonAugmentedHessian period hPeriod
      configuration data analysis chart sameAction physical
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (diagonalPureGhostCore period hPeriod configuration analysis ghost))
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis test) = 0 := by
  rw [globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed,
    diagonalExtendedBulkH13GaugeFixed_eq_graph_add_sevenPhysical,
    diagonalPureGhostCore_physicalHessian_left_zero, add_zero]
  simpa [diagonalExtendedBulkGraphHessianOnCore,
    diagonalExtendedBulkHessian_apply, diagonalPureGhostCore] using
    diagonalPureGhost_hessian_zero period hPeriod couplings
      (globalCandidateAMetricBySector period hPeriod data) hMetric hWeights ghost test.1

/-- The vanishing survives completion and the full physical augmentation. -/
theorem diagonalPureGhostCore_augmented_riesz_zero
    (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
      globalCandidateAMetricBySector period hPeriod data .minus)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings = 0)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    globalCandidateACommonAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (diagonalPureGhostCore period hPeriod configuration analysis ghost)) = 0 := by
  let state := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
    (diagonalPureGhostCore period hPeriod configuration analysis ghost)
  have hRow : (globalCandidateACommonAugmentedHessian period hPeriod
      configuration data analysis chart sameAction physical state : _ → Real) = fun _ => 0 := by
    apply (diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis).equalizer
      (globalCandidateACommonAugmentedHessian period hPeriod
        configuration data analysis chart sameAction physical state).continuous continuous_const
    funext test
    exact diagonalPureGhostCore_augmented_pairing_zero period hPeriod configuration
      data analysis chart sameAction physical hMetric hWeights ghost test
  apply ext_inner_right Real
  intro test
  rw [inner_zero_left, globalCandidateACommonAugmentedRieszOperator_pairing]
  exact congrFun hRow test

/-- No ghost is lost in the embedding into the augmented kernel. -/
theorem diagonalGhost_injects_into_augmented_kernel
    (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
      globalCandidateAMetricBySector period hPeriod data .minus)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings = 0) :
    ∃ inclusion : GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
      (globalCandidateACommonAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).ker,
      Function.Injective inclusion := by
  let coreMap : GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
    (LinearMap.inl Real _ _).comp (diagonalPureGhost period hPeriod)
  let embedded := (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis).comp coreMap
  have hEmbedded : Function.Injective embedded := by
    intro first second hEqual
    have hCore := diagonalExtendedBulkL2SmoothEmbedding_injective period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis hEqual
    exact diagonalPureGhost_injective period hPeriod (congrArg Prod.fst hCore)
  let inclusion := embedded.codRestrict
    (globalCandidateACommonAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical).ker (by
        intro ghost
        exact diagonalPureGhostCore_augmented_riesz_zero period hPeriod configuration
          data analysis chart sameAction physical hMetric hWeights ghost)
  refine ⟨inclusion, ?_⟩
  intro first second hEqual
  exact hEmbedded (congrArg Subtype.val hEqual)

end
end P0EFTJanusProgramPT12DiagonalGhostPhysicalKernel4D
end JanusFormal
