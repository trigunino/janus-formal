import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedSmoothCoreHilbertCompletion4D

/-!
# Completed reduced matter and LL actions

The physical feature projection is unchanged by orthogonal reduction.  Its
matter and LL coordinates therefore define genuine smooth actions on the
reduced Hilbert completion and recover the established graph actions on the
dense quotient core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMatterLLAction4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedSmoothCoreHilbertCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)

private abbrev Metric :=
  globalCandidateAMetricBySector period hPeriod data

local instance completedClosedNullIsClosed : IsClosed
    (globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
      configuration data analysis : Set
        (CommonAugmentedHilbert period hPeriod configuration data analysis)) :=
  Submodule.isClosed_topologicalClosure _

local instance completedLLNormedSpace : NormedSpace Real
    (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (globalFullLLGraphInnerProductSpace period hPeriod data analysis).toNormedSpace

/-- Orthogonal reduction changes a common state only by a vector in the
closed null space. -/
theorem common_sub_minimalPhysicalReduction_mem_closedNull
    (state : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    state -
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state :
            CommonAugmentedHilbert period hPeriod configuration data
              analysis) ∈
      globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
        configuration data analysis := by
  rw [← globalCandidateAMinimalPhysicalHilbertReduction_ker period hPeriod
    configuration data analysis]
  apply LinearMap.mem_ker.mpr
  rw [map_sub]
  have hId :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis state)
  change
    globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) =
      globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis state at hId
  change
    globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state -
        globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
            configuration data analysis state) = 0
  rw [hId, sub_self]

/-- Every completed physical feature is invariant under the canonical
orthogonal reduction. -/
theorem globalCandidateAMinimalPhysicalFeatureProjection_reduction
    (state : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) =
      globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis state := by
  have hClosed :=
    common_sub_minimalPhysicalReduction_mem_closedNull period hPeriod
      configuration data analysis state
  have hKernel :=
    globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule_le_feature_ker
      period hPeriod configuration data analysis hClosed
  have hZero := LinearMap.mem_ker.mp hKernel
  rw [map_sub] at hZero
  exact (sub_eq_zero.mp hZero).symm

/-- Inclusion of the reduced Hilbert representative into the common
completion. -/
def globalCandidateAMinimalPhysicalReducedHilbertInclusion :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis
    :=
  (globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
    configuration data analysis).orthogonal.subtypeL

/-- All completed physical features of a reduced representative. -/
def globalCandidateAMinimalPhysicalReducedFeatureProjection :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real]
      GlobalCandidateAMinimalPhysicalFeatureHilbert period hPeriod
        configuration data analysis :=
  (globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
    configuration data analysis).comp
    (globalCandidateAMinimalPhysicalReducedHilbertInclusion period hPeriod
      configuration data analysis)

private def minimalPhysicalFeatureMatterProjection :
    GlobalCandidateAMinimalPhysicalFeatureHilbert period hPeriod
        configuration data analysis →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared where
  toFun value := value.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.comp (continuous_snd.comp continuous_snd)

private def minimalPhysicalFeatureLLProjection :
    GlobalCandidateAMinimalPhysicalFeatureHilbert period hPeriod
        configuration data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis where
  toFun value := value.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_snd.comp (continuous_snd.comp continuous_snd)

/-- Completed primitive-matter coordinate on the reduced Hilbert space. -/
def globalCandidateAMinimalPhysicalReducedMatterProjection :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared :=
  (minimalPhysicalFeatureMatterProjection period hPeriod configuration data
    analysis).comp
    (globalCandidateAMinimalPhysicalReducedFeatureProjection period hPeriod
      configuration data analysis)

/-- Completed full-LL coordinate on the reduced Hilbert space. -/
def globalCandidateAMinimalPhysicalReducedLLProjection :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
  (minimalPhysicalFeatureLLProjection period hPeriod configuration data
    analysis).comp
    (globalCandidateAMinimalPhysicalReducedFeatureProjection period hPeriod
      configuration data analysis)

@[simp]
theorem globalCandidateAMinimalPhysicalReducedMatterProjection_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedMatterProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
        couplings.matterMassSquared core.2.2.1 := by
  rw [globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
  have hFeature :=
    globalCandidateAMinimalPhysicalFeatureProjection_reduction period hPeriod
      configuration data analysis
      (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
        configuration data analysis core)
  have hMatter := congrArg (fun value => value.2.2.1) hFeature
  change
    (globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
            configuration data analysis core))).2.2.1 =
      programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
        couplings.matterMassSquared core.2.2.1
  simpa only [globalCandidateAMinimalPhysicalFeatureProjection_smooth] using
    hMatter

@[simp]
theorem globalCandidateAMinimalPhysicalReducedLLProjection_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedLLProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        core.2.2.2 := by
  rw [globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
  have hFeature :=
    globalCandidateAMinimalPhysicalFeatureProjection_reduction period hPeriod
      configuration data analysis
      (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
        configuration data analysis core)
  have hLL := congrArg (fun value => value.2.2.2) hFeature
  change
    (globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
            configuration data analysis core))).2.2.2 =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        core.2.2.2
  simpa only [globalCandidateAMinimalPhysicalFeatureProjection_smooth] using
    hLL

/-- Genuine completed primitive-matter action on the reduced Hilbert space. -/
def globalCandidateAMinimalPhysicalReducedCompletedMatterAction :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis → Real :=
  fun state =>
    programPPrimitiveSpinCMatterGraphAction period hPeriod
      couplings.matterMassSquared
      (globalCandidateAMinimalPhysicalReducedMatterProjection period hPeriod
        configuration data analysis state)

/-- Genuine completed full-LL action on the reduced Hilbert space. -/
def globalCandidateAMinimalPhysicalReducedCompletedLLAction :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis → Real :=
  fun state =>
    globalCandidateAFullLLGraphAction period hPeriod data analysis
      (globalCandidateAMinimalPhysicalReducedLLProjection period hPeriod
        configuration data analysis state)

theorem globalCandidateAMinimalPhysicalReducedCompletedMatterAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedMatterAction period
        hPeriod configuration data analysis) := by
  exact
    (programPPrimitiveSpinCMatterGraphAction_contDiff_two period hPeriod
      couplings.matterMassSquared).comp
        (globalCandidateAMinimalPhysicalReducedMatterProjection period hPeriod
          configuration data analysis).contDiff

theorem globalCandidateAMinimalPhysicalReducedCompletedLLAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedLLAction period hPeriod
        configuration data analysis) := by
  have hProjection : ContDiff Real ⊤
      (globalCandidateAMinimalPhysicalReducedLLProjection period hPeriod
        configuration data analysis) :=
    @ContinuousLinearMap.contDiff Real
      (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis)
      (GlobalFullLLGraphHilbert period hPeriod data analysis)
      inferInstance inferInstance inferInstance inferInstance
      (completedLLNormedSpace period hPeriod configuration data analysis) ⊤
      (globalCandidateAMinimalPhysicalReducedLLProjection period hPeriod
        configuration data analysis)
  exact
    (globalCandidateAFullLLGraphAction_contDiff_two period hPeriod data
      analysis).comp (hProjection.of_le (by simp))

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedMatterAction_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedMatterAction period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      programPPrimitiveSpinCMatterGraphAction period hPeriod
        couplings.matterMassSquared
        (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
          couplings.matterMassSquared core.2.2.1) := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedMatterAction,
    globalCandidateAMinimalPhysicalReducedMatterProjection_core]

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedLLAction_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedLLAction period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      globalCandidateAFullLLGraphAction period hPeriod data analysis
        (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
          core.2.2.2) := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedLLAction,
    globalCandidateAMinimalPhysicalReducedLLProjection_core]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMatterLLAction4D
end JanusFormal
