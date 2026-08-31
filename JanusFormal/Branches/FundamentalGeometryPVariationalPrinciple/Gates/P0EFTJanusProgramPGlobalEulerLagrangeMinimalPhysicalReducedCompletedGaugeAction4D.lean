import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMatterLLAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairingC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianLorenzGraphC2Chart4D

/-!
# Completed reduced gauge actions

The two de Donder graph coordinates already belong to their faithful Hilbert
graphs.  The Abelian coordinate is projected canonically onto the closed
Lorenz graph.  Their established quadratic actions therefore pull back to
genuine `C²` actions on the minimal physical reduced Hilbert completion and
recover the smooth graph actions on the quotient core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGaugeAction4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairingC2Chart4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedSmoothCoreHilbertCompletion4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMatterLLAction4D

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

local instance completedPlusMetricGraphNormedSpace :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
        (Metric period hPeriod configuration data .plus)) :=
  (inferInstance : InnerProductSpace Real
    (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
      (Metric period hPeriod configuration data .plus))).toNormedSpace

local instance completedPlusMetricGraphModule :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
        (Metric period hPeriod configuration data .plus)) :=
  (inferInstance : InnerProductSpace Real
    (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
      (Metric period hPeriod configuration data .plus))).toNormedSpace.toModule

local instance completedMinusMetricGraphNormedSpace :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
        (Metric period hPeriod configuration data .minus)) :=
  (inferInstance : InnerProductSpace Real
    (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
      (Metric period hPeriod configuration data .minus))).toNormedSpace

local instance completedMinusMetricGraphModule :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
        (Metric period hPeriod configuration data .minus)) :=
  (inferInstance : InnerProductSpace Real
    (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
      (Metric period hPeriod configuration data .minus))).toNormedSpace.toModule

local instance completedAbelianAmbientNormedSpace :
    NormedSpace Real (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)).toNormedSpace

local instance completedAbelianAmbientModule :
    Module Real (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)).toNormedSpace.toModule

local instance completedAbelianGraphNormedSpace :
    NormedSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod
        (Metric period hPeriod configuration data)) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianLorenzGraphHilbert period hPeriod
      (Metric period hPeriod configuration data))).toNormedSpace

local instance completedAbelianGraphModule :
    Module Real
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod
        (Metric period hPeriod configuration data)) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianLorenzGraphHilbert period hPeriod
      (Metric period hPeriod configuration data))).toNormedSpace.toModule

local instance completedAbelianGraphIsClosed : IsClosed
    (globalPairedAbelianLorenzGraphSubmodule period hPeriod
      (Metric period hPeriod configuration data) :
        Set (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)) :=
  Submodule.isClosed_topologicalClosure _

private def minimalPhysicalFeaturePlusMetricProjection :
    GlobalCandidateAMinimalPhysicalFeatureHilbert period hPeriod
        configuration data analysis →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
        (Metric period hPeriod configuration data .plus) where
  toFun value := value.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.comp continuous_fst

private def minimalPhysicalFeatureMinusMetricProjection :
    GlobalCandidateAMinimalPhysicalFeatureHilbert period hPeriod
        configuration data analysis →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
        (Metric period hPeriod configuration data .minus) where
  toFun value := value.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_snd.comp continuous_fst

private def minimalPhysicalFeatureAbelianAmbientProjection :
    GlobalCandidateAMinimalPhysicalFeatureHilbert period hPeriod
        configuration data analysis →L[Real]
      GlobalPairedAbelianLorenzGraphAmbient period hPeriod where
  toFun value := value.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.comp continuous_snd

/-- Completed positive-sector de Donder graph coordinate. -/
def globalCandidateAMinimalPhysicalReducedPlusMetricProjection :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
        (Metric period hPeriod configuration data .plus) :=
  (minimalPhysicalFeaturePlusMetricProjection period hPeriod configuration
    data analysis).comp
    (globalCandidateAMinimalPhysicalReducedFeatureProjection period hPeriod
      configuration data analysis)

/-- Completed negative-sector de Donder graph coordinate. -/
def globalCandidateAMinimalPhysicalReducedMinusMetricProjection :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
        (Metric period hPeriod configuration data .minus) :=
  (minimalPhysicalFeatureMinusMetricProjection period hPeriod configuration
    data analysis).comp
    (globalCandidateAMinimalPhysicalReducedFeatureProjection period hPeriod
      configuration data analysis)

/-- Completed Abelian potential/Lorenz ambient coordinate. -/
def globalCandidateAMinimalPhysicalReducedAbelianAmbientProjection :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real]
      GlobalPairedAbelianLorenzGraphAmbient period hPeriod :=
  (minimalPhysicalFeatureAbelianAmbientProjection period hPeriod
    configuration data analysis).comp
    (globalCandidateAMinimalPhysicalReducedFeatureProjection period hPeriod
      configuration data analysis)

/-- Canonical projection of the completed Abelian coordinate onto its closed
faithful Lorenz graph. -/
def globalCandidateAMinimalPhysicalReducedAbelianProjection :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real]
      GlobalPairedAbelianLorenzGraphHilbert period hPeriod
        (Metric period hPeriod configuration data) :=
  (globalPairedAbelianLorenzGraphSubmodule period hPeriod
      (Metric period hPeriod configuration data)).orthogonalProjectionOnto.comp
    (globalCandidateAMinimalPhysicalReducedAbelianAmbientProjection period
      hPeriod configuration data analysis)

@[simp]
theorem globalCandidateAMinimalPhysicalReducedPlusMetricProjection_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedPlusMetricProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      globalGeneralMetricDeDonderPairingSmoothEmbedding period hPeriod
        (Metric period hPeriod configuration data .plus)
        (core.1.metricPerturbation .plus) := by
  rw [globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
  have hFeature :=
    globalCandidateAMinimalPhysicalFeatureProjection_reduction period hPeriod
      configuration data analysis
      (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
        configuration data analysis core)
  have hPlus := congrArg (fun value => value.1.1) hFeature
  change
    (globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
            configuration data analysis core))).1.1 = _
  simpa only [globalCandidateAMinimalPhysicalFeatureProjection_smooth] using
    hPlus

@[simp]
theorem globalCandidateAMinimalPhysicalReducedMinusMetricProjection_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedMinusMetricProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      globalGeneralMetricDeDonderPairingSmoothEmbedding period hPeriod
        (Metric period hPeriod configuration data .minus)
        (core.1.metricPerturbation .minus) := by
  rw [globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
  have hFeature :=
    globalCandidateAMinimalPhysicalFeatureProjection_reduction period hPeriod
      configuration data analysis
      (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
        configuration data analysis core)
  have hMinus := congrArg (fun value => value.1.2) hFeature
  change
    (globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
            configuration data analysis core))).1.2 = _
  simpa only [globalCandidateAMinimalPhysicalFeatureProjection_smooth] using
    hMinus

@[simp]
theorem globalCandidateAMinimalPhysicalReducedAbelianAmbientProjection_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedAbelianAmbientProjection period
        hPeriod configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod
        (Metric period hPeriod configuration data) core.2.1.potential := by
  rw [globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
  have hFeature :=
    globalCandidateAMinimalPhysicalFeatureProjection_reduction period hPeriod
      configuration data analysis
      (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
        configuration data analysis core)
  have hAbelian := congrArg (fun value => value.2.1) hFeature
  change
    (globalCandidateAMinimalPhysicalFeatureProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
            configuration data analysis core))).2.1 = _
  simpa only [globalCandidateAMinimalPhysicalFeatureProjection_smooth] using
    hAbelian

@[simp]
theorem globalCandidateAMinimalPhysicalReducedAbelianProjection_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedAbelianProjection period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      globalPairedAbelianLorenzSmoothEmbedding period hPeriod
        (Metric period hPeriod configuration data) core.2.1.potential := by
  change
    (globalPairedAbelianLorenzGraphSubmodule period hPeriod
        (Metric period hPeriod configuration data)).orthogonalProjectionOnto
      (globalCandidateAMinimalPhysicalReducedAbelianAmbientProjection period
        hPeriod configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core))) = _
  rw [globalCandidateAMinimalPhysicalReducedAbelianAmbientProjection_core]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (globalPairedAbelianLorenzSmoothEmbedding period hPeriod
      (Metric period hPeriod configuration data) core.2.1.potential)

/-- Positive-sector completed de Donder gauge action. -/
def globalCandidateAMinimalPhysicalReducedCompletedPlusDeDonderAction :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis → Real :=
  fun state =>
    globalGeneralMetricDeDonderPairingGraphAction period hPeriod
      (Metric period hPeriod configuration data .plus)
      (globalCandidateAMinimalPhysicalReducedPlusMetricProjection period
        hPeriod configuration data analysis state)

/-- Negative-sector completed de Donder gauge action. -/
def globalCandidateAMinimalPhysicalReducedCompletedMinusDeDonderAction :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis → Real :=
  fun state =>
    globalGeneralMetricDeDonderPairingGraphAction period hPeriod
      (Metric period hPeriod configuration data .minus)
      (globalCandidateAMinimalPhysicalReducedMinusMetricProjection period
        hPeriod configuration data analysis state)

/-- Completed paired Abelian Lorenz gauge action. -/
def globalCandidateAMinimalPhysicalReducedCompletedAbelianLorenzAction :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis → Real :=
  fun state =>
    globalPairedAbelianLorenzGraphAction period hPeriod
      (Metric period hPeriod configuration data)
      (globalCandidateAMinimalPhysicalReducedAbelianProjection period hPeriod
        configuration data analysis state)

/-- Sum of the three completed physical gauge actions. -/
def globalCandidateAMinimalPhysicalReducedCompletedGaugeAction :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis → Real :=
  fun state =>
    globalCandidateAMinimalPhysicalReducedCompletedPlusDeDonderAction period
        hPeriod configuration data analysis state +
      globalCandidateAMinimalPhysicalReducedCompletedMinusDeDonderAction period
        hPeriod configuration data analysis state +
      globalCandidateAMinimalPhysicalReducedCompletedAbelianLorenzAction period
        hPeriod configuration data analysis state

/-- Sum of every physical graph action currently extended to the reduced
Hilbert completion: de Donder in both sectors, Lorenz, matter and LL. -/
def globalCandidateAMinimalPhysicalReducedCompletedGraphAction :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis → Real :=
  fun state =>
    globalCandidateAMinimalPhysicalReducedCompletedGaugeAction period hPeriod
        configuration data analysis state +
      globalCandidateAMinimalPhysicalReducedCompletedMatterAction period
        hPeriod configuration data analysis state +
      globalCandidateAMinimalPhysicalReducedCompletedLLAction period hPeriod
        configuration data analysis state

theorem globalCandidateAMinimalPhysicalReducedCompletedPlusDeDonderAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedPlusDeDonderAction period
        hPeriod configuration data analysis) := by
  have hProjection : ContDiff Real ⊤
      (globalCandidateAMinimalPhysicalReducedPlusMetricProjection period
        hPeriod configuration data analysis) :=
    @ContinuousLinearMap.contDiff Real
      (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis)
      (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
        (Metric period hPeriod configuration data .plus))
      inferInstance inferInstance inferInstance inferInstance
      (completedPlusMetricGraphNormedSpace period hPeriod configuration data) ⊤
      (globalCandidateAMinimalPhysicalReducedPlusMetricProjection period
        hPeriod configuration data analysis)
  exact
    (globalGeneralMetricDeDonderPairingGraphAction_contDiff_two period hPeriod
      (Metric period hPeriod configuration data .plus)).comp
        (hProjection.of_le (by simp))

theorem globalCandidateAMinimalPhysicalReducedCompletedMinusDeDonderAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedMinusDeDonderAction period
        hPeriod configuration data analysis) := by
  have hProjection : ContDiff Real ⊤
      (globalCandidateAMinimalPhysicalReducedMinusMetricProjection period
        hPeriod configuration data analysis) :=
    @ContinuousLinearMap.contDiff Real
      (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis)
      (GlobalGeneralMetricDeDonderPairingGraphHilbert period hPeriod
        (Metric period hPeriod configuration data .minus))
      inferInstance inferInstance inferInstance inferInstance
      (completedMinusMetricGraphNormedSpace period hPeriod configuration data) ⊤
      (globalCandidateAMinimalPhysicalReducedMinusMetricProjection period
        hPeriod configuration data analysis)
  exact
    (globalGeneralMetricDeDonderPairingGraphAction_contDiff_two period hPeriod
      (Metric period hPeriod configuration data .minus)).comp
        (hProjection.of_le (by simp))

theorem globalCandidateAMinimalPhysicalReducedCompletedAbelianLorenzAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedAbelianLorenzAction period
        hPeriod configuration data analysis) := by
  exact
    (globalPairedAbelianLorenzGraphAction_contDiff_two period hPeriod
      (Metric period hPeriod configuration data)).comp
        (globalCandidateAMinimalPhysicalReducedAbelianProjection period hPeriod
          configuration data analysis).contDiff

theorem globalCandidateAMinimalPhysicalReducedCompletedGaugeAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedGaugeAction period
        hPeriod configuration data analysis) := by
  exact
    ((globalCandidateAMinimalPhysicalReducedCompletedPlusDeDonderAction_contDiff_two
      period hPeriod configuration data analysis).add
      (globalCandidateAMinimalPhysicalReducedCompletedMinusDeDonderAction_contDiff_two
        period hPeriod configuration data analysis)).add
      (globalCandidateAMinimalPhysicalReducedCompletedAbelianLorenzAction_contDiff_two
        period hPeriod configuration data analysis)

theorem globalCandidateAMinimalPhysicalReducedCompletedGraphAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedGraphAction period
        hPeriod configuration data analysis) := by
  exact
    ((globalCandidateAMinimalPhysicalReducedCompletedGaugeAction_contDiff_two
      period hPeriod configuration data analysis).add
      (globalCandidateAMinimalPhysicalReducedCompletedMatterAction_contDiff_two
        period hPeriod configuration data analysis)).add
      (globalCandidateAMinimalPhysicalReducedCompletedLLAction_contDiff_two
        period hPeriod configuration data analysis)

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedGaugeAction_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedGaugeAction period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      globalGeneralMetricDeDonderPairingGraphAction period hPeriod
          (Metric period hPeriod configuration data .plus)
          (globalGeneralMetricDeDonderPairingSmoothEmbedding period hPeriod
            (Metric period hPeriod configuration data .plus)
            (core.1.metricPerturbation .plus)) +
        globalGeneralMetricDeDonderPairingGraphAction period hPeriod
          (Metric period hPeriod configuration data .minus)
          (globalGeneralMetricDeDonderPairingSmoothEmbedding period hPeriod
            (Metric period hPeriod configuration data .minus)
            (core.1.metricPerturbation .minus)) +
        globalPairedAbelianLorenzGraphAction period hPeriod
          (Metric period hPeriod configuration data)
          (globalPairedAbelianLorenzSmoothEmbedding period hPeriod
            (Metric period hPeriod configuration data) core.2.1.potential) := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedGaugeAction,
    globalCandidateAMinimalPhysicalReducedCompletedPlusDeDonderAction,
    globalCandidateAMinimalPhysicalReducedCompletedMinusDeDonderAction,
    globalCandidateAMinimalPhysicalReducedCompletedAbelianLorenzAction,
    globalCandidateAMinimalPhysicalReducedPlusMetricProjection_core,
    globalCandidateAMinimalPhysicalReducedMinusMetricProjection_core,
    globalCandidateAMinimalPhysicalReducedAbelianProjection_core]

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedGraphAction_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedGraphAction period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      globalCandidateAMinimalPhysicalReducedCompletedGaugeAction period hPeriod
          configuration data analysis
          (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
            period hPeriod configuration data analysis
            (Submodule.Quotient.mk core)) +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
            couplings.matterMassSquared core.2.2.1) +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            core.2.2.2) := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedGraphAction,
    globalCandidateAMinimalPhysicalReducedCompletedMatterAction_core,
    globalCandidateAMinimalPhysicalReducedCompletedLLAction_core]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGaugeAction4D
end JanusFormal
