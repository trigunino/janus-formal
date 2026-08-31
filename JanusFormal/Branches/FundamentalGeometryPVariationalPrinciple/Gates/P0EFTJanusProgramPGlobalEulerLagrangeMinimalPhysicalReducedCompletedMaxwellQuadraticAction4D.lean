import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRobinAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D

/-!
# Reduced Maxwell Hessian quadratic actions

Any supplied bounded Maxwell Hessian extensions annihilate the closed
minimal-physical null space because their smooth targets factor through the
minimal physical tangent.  They therefore descend canonically to bounded
symmetric forms on the reduced Hilbert completion.  Their quadratic energies
are smooth and recover the exact Maxwell Hessian quadratic energies on the
quotient core.  No nonlinear completed Maxwell action is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMaxwellQuadraticAction4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open Filter Set Topology MeasureTheory
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
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
open P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedSmoothCoreHilbertCompletion4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMatterLLAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRobinAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)

private abbrev Core :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev Common :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

private abbrev Reduced :=
  GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
    data analysis

variable
    (maxwellPlus :
      GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
        configuration data analysis
        (diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
          configuration data analysis chart sameAction))
    (maxwellMinus :
      GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
        configuration data analysis
        (diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
          configuration data analysis chart sameAction))

private theorem maxwellPlus_core_left_zero
    (first second : Core period hPeriod configuration analysis)
    (hFirst : first ∈
      globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis) :
    diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
        configuration data analysis chart sameAction first second = 0 := by
  have hTangent := LinearMap.mem_ker.mp hFirst
  unfold diagonalExtendedBulkH11MaxwellPlusHessianOnCore
  change
    globalCandidateAH11LocalMaxwellPlusHessian period hPeriod chart
      sameAction.chartBridge.basePoint
      (sameAction.chartBridge.tangentAnalysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis first))
      (sameAction.chartBridge.tangentAnalysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis second)) = 0
  simp [hTangent]

private theorem maxwellMinus_core_left_zero
    (first second : Core period hPeriod configuration analysis)
    (hFirst : first ∈
      globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis) :
    diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
        configuration data analysis chart sameAction first second = 0 := by
  have hTangent := LinearMap.mem_ker.mp hFirst
  unfold diagonalExtendedBulkH11MaxwellMinusHessianOnCore
  change
    globalCandidateAH11LocalMaxwellMinusHessian period hPeriod chart
      sameAction.chartBridge.basePoint
      (sameAction.chartBridge.tangentAnalysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis first))
      (sameAction.chartBridge.tangentAnalysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis second)) = 0
  simp [hTangent]

/-- Any bounded block whose core target kills the minimal tangent kernel also
kills its closed Hilbert null span. -/
private theorem block_closedNull_le_form_ker
    (target : Core period hPeriod configuration analysis →
      Core period hPeriod configuration analysis → Real)
    (block : GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
      configuration data analysis target)
    (hTarget : ∀ first second,
      first ∈ globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
          configuration data analysis →
        target first second = 0) :
    globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
        configuration data analysis ≤
      block.form.ker := by
  have hDense : DenseRange
      (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
        configuration data analysis) :=
    diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
  unfold globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule
  apply Submodule.topologicalClosure_minimal
  · intro state hState
    rcases hState with ⟨core, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hFunctions :
        (fun test : Common period hPeriod configuration data analysis =>
          block.form
            (globalCandidateAMinimalPhysicalNullHilbertLinearMap period hPeriod
              configuration data analysis core) test) =
        (fun _ => (0 : Real)) := by
      apply hDense.equalizer
      · exact
          (block.form
            (globalCandidateAMinimalPhysicalNullHilbertLinearMap period hPeriod
              configuration data analysis core)).continuous
      · exact continuous_const
      · funext second
        change
          block.form
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis core.1)
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis second) = 0
        rw [block.smooth_agreement core.1 second]
        exact hTarget core.1 second core.2
    exact ContinuousLinearMap.ext (congrFun hFunctions)
  · exact block.form.isClosed_ker

private theorem block_form_reduction_left
    {target : Core period hPeriod configuration analysis →
      Core period hPeriod configuration analysis → Real}
    (block : GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
      configuration data analysis target)
    (hClosed :
      globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
          configuration data analysis ≤ block.form.ker)
    (state : Common period hPeriod configuration data analysis) :
    block.form
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) =
      block.form state := by
  have hMem := hClosed
    (common_sub_minimalPhysicalReduction_mem_closedNull period hPeriod
      configuration data analysis state)
  have hZero := LinearMap.mem_ker.mp hMem
  rw [map_sub] at hZero
  exact (sub_eq_zero.mp hZero).symm

private theorem block_form_reduction_right
    {target : Core period hPeriod configuration analysis →
      Core period hPeriod configuration analysis → Real}
    (block : GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
      configuration data analysis target)
    (hClosed :
      globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
          configuration data analysis ≤ block.form.ker)
    (state test : Common period hPeriod configuration data analysis) :
    block.form test
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) =
      block.form test state := by
  rw [block.symmetric test
      (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis state),
    block.symmetric test state]
  exact congrArg (fun functional => functional test)
    (block_form_reduction_left period hPeriod configuration data analysis block
      hClosed state)

/-- Restriction of a bounded common-domain physical block form to the reduced
minimal-physical Hilbert completion. -/
def reducedBlockForm
    {target : Core period hPeriod configuration analysis →
      Core period hPeriod configuration analysis → Real}
    (block : GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
      configuration data analysis target) :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  block.form.bilinearComp
    (globalCandidateAMinimalPhysicalReducedHilbertInclusion period hPeriod
      configuration data analysis)
    (globalCandidateAMinimalPhysicalReducedHilbertInclusion period hPeriod
      configuration data analysis)

/-- Bounded positive-sector Maxwell Hessian on the reduced completion. -/
def globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusHessian :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  reducedBlockForm period hPeriod configuration data analysis maxwellPlus

/-- Bounded negative-sector Maxwell Hessian on the reduced completion. -/
def globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusHessian :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  reducedBlockForm period hPeriod configuration data analysis maxwellMinus

/-- Exact smooth-core agreement for a reduced block whose target kills the
minimal-physical core kernel. -/
theorem reducedBlockForm_core
    (target : Core period hPeriod configuration analysis →
      Core period hPeriod configuration analysis → Real)
    (block : GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
      configuration data analysis target)
    (hTarget : ∀ first second,
      first ∈ globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
          configuration data analysis →
        target first second = 0)
    (first second : Core period hPeriod configuration analysis) :
    reducedBlockForm period hPeriod configuration data analysis block
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk second)) =
      target first second := by
  rw [globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk,
    globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
  change
    block.form
      (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis
        (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis first))
      (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis
        (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis second)) = _
  have hClosed := block_closedNull_le_form_ker period hPeriod configuration data
    analysis target block hTarget
  rw [block_form_reduction_left period hPeriod configuration data analysis
      block hClosed,
    block_form_reduction_right period hPeriod configuration data analysis
      block hClosed]
  change
    block.form
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis first)
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis second) = target first second
  exact block.smooth_agreement first second

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusHessian_core
    (first second : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusHessian period
        hPeriod configuration data analysis chart sameAction maxwellPlus
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk second)) =
      diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
        configuration data analysis chart sameAction first second := by
  exact reducedBlockForm_core period hPeriod configuration data analysis
    (diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
      configuration data analysis chart sameAction) maxwellPlus
    (maxwellPlus_core_left_zero period hPeriod configuration data analysis
      chart sameAction) first second

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusHessian_core
    (first second : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusHessian period
        hPeriod configuration data analysis chart sameAction maxwellMinus
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk second)) =
      diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
        configuration data analysis chart sameAction first second := by
  exact reducedBlockForm_core period hPeriod configuration data analysis
    (diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
      configuration data analysis chart sameAction) maxwellMinus
    (maxwellMinus_core_left_zero period hPeriod configuration data analysis
      chart sameAction) first second

/-- Positive Maxwell Hessian quadratic energy on the reduced completion. -/
def globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusQuadraticAction :
    Reduced period hPeriod configuration data analysis → Real :=
  fun state => (1 / 2 : Real) *
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusHessian period
      hPeriod configuration data analysis chart sameAction maxwellPlus state state

/-- Negative Maxwell Hessian quadratic energy on the reduced completion. -/
def globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusQuadraticAction :
    Reduced period hPeriod configuration data analysis → Real :=
  fun state => (1 / 2 : Real) *
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusHessian period
      hPeriod configuration data analysis chart sameAction maxwellMinus state state

/-- Sum of both reduced Maxwell Hessian quadratic energies. -/
def globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction :
    Reduced period hPeriod configuration data analysis → Real :=
  fun state =>
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusQuadraticAction
        period hPeriod configuration data analysis chart sameAction maxwellPlus
          state +
      globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusQuadraticAction
        period hPeriod configuration data analysis chart sameAction maxwellMinus
          state

theorem globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusQuadraticAction_contDiff :
    ContDiff Real ⊤
      (globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusQuadraticAction
        period hPeriod configuration data analysis chart sameAction
          maxwellPlus) := by
  unfold globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusQuadraticAction
  exact contDiff_const.mul
    ((globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusHessian period
      hPeriod configuration data analysis chart sameAction maxwellPlus
      ).contDiff.clm_apply contDiff_id)

theorem globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusQuadraticAction_contDiff :
    ContDiff Real ⊤
      (globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusQuadraticAction
        period hPeriod configuration data analysis chart sameAction
          maxwellMinus) := by
  unfold globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusQuadraticAction
  exact contDiff_const.mul
    ((globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusHessian period
      hPeriod configuration data analysis chart sameAction maxwellMinus
      ).contDiff.clm_apply contDiff_id)

theorem globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction
        period hPeriod configuration data analysis chart sameAction maxwellPlus
          maxwellMinus) := by
  exact
    ((globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusQuadraticAction_contDiff
      period hPeriod configuration data analysis chart sameAction
        maxwellPlus).add
      (globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusQuadraticAction_contDiff
        period hPeriod configuration data analysis chart sameAction
          maxwellMinus)).of_le (by simp)

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction_core
    (core : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction period
        hPeriod configuration data analysis chart sameAction maxwellPlus
          maxwellMinus
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      (1 / 2 : Real) *
          diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
            configuration data analysis chart sameAction core core +
        (1 / 2 : Real) *
          diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
            configuration data analysis chart sameAction core core := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedMaxwellQuadraticAction,
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusQuadraticAction,
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusQuadraticAction,
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellPlusHessian_core,
    globalCandidateAMinimalPhysicalReducedCompletedMaxwellMinusHessian_core]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMaxwellQuadraticAction4D
end JanusFormal
