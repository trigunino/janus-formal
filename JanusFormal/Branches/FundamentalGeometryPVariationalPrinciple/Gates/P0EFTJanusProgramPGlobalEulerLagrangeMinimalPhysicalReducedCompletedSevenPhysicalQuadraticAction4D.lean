import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMaxwellQuadraticAction4D

/-!
# Reduced seven-physical-block Hessian quadratic action

Seven supplied bounded H11 block extensions canonically sum to the full
physical Hessian extension.  Because the smooth physical Hessian factors
through the minimal tangent, this sum annihilates the closed physical null
space and descends to the reduced Hilbert completion.  Its quadratic energy is
smooth and agrees exactly with the full seven-block Hessian energy on the
quotient core.  This is a base-point quadratic action, not a nonlinear
completion of the seven physical action blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

universe u

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
open P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedSmoothCoreHilbertCompletion4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMatterLLAction4D

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

/-- Derivative of the quadratic action associated to a bounded symmetric
bilinear form. -/
theorem symmetricQuadratic_hasFDerivAt
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (form : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second, form first second = form second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * form state state)
      (form point) point := by
  have hDiagonal :=
    (form.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (form point direction + form direction point) = form point direction
  rw [hSymmetric direction point]
  ring

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
    (blocks : GlobalCandidateASevenPhysicalBlockExtensions4D period hPeriod
      configuration data analysis chart sameAction)

private abbrev Core :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev Common :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

private abbrev Reduced :=
  GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
    data analysis

private def sevenPhysicalExtension :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_blocks period hPeriod
    configuration data analysis chart sameAction blocks

private theorem sevenPhysical_core_left_zero
    (first second : Core period hPeriod configuration analysis)
    (hFirst : first ∈
      globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second = 0 := by
  have hTangent := LinearMap.mem_ker.mp hFirst
  unfold diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
  simp [hTangent]

private theorem sevenPhysical_closedNull_le_form_ker :
    globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
        configuration data analysis ≤
      (sevenPhysicalExtension period hPeriod configuration data analysis chart
        sameAction blocks).form.ker := by
  let physical := sevenPhysicalExtension period hPeriod configuration data
    analysis chart sameAction blocks
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
          physical.form
            (globalCandidateAMinimalPhysicalNullHilbertLinearMap period hPeriod
              configuration data analysis core) test) =
        (fun _ => (0 : Real)) := by
      apply hDense.equalizer
      · exact
          (physical.form
            (globalCandidateAMinimalPhysicalNullHilbertLinearMap period hPeriod
              configuration data analysis core)).continuous
      · exact continuous_const
      · funext second
        change
          physical.form
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis core.1)
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis second) = 0
        rw [physical.smooth_agreement core.1 second]
        exact sevenPhysical_core_left_zero period hPeriod configuration data
          analysis chart sameAction core.1 second core.2
    exact ContinuousLinearMap.ext (congrFun hFunctions)
  · exact physical.form.isClosed_ker

private theorem sevenPhysical_form_reduction_left
    (state : Common period hPeriod configuration data analysis) :
    (sevenPhysicalExtension period hPeriod configuration data analysis chart
        sameAction blocks).form
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) =
      (sevenPhysicalExtension period hPeriod configuration data analysis chart
        sameAction blocks).form state := by
  have hMem := sevenPhysical_closedNull_le_form_ker period hPeriod
    configuration data analysis chart sameAction blocks
      (common_sub_minimalPhysicalReduction_mem_closedNull period hPeriod
        configuration data analysis state)
  have hZero := LinearMap.mem_ker.mp hMem
  rw [map_sub] at hZero
  exact (sub_eq_zero.mp hZero).symm

private theorem sevenPhysical_form_reduction_right
    (state test : Common period hPeriod configuration data analysis) :
    (sevenPhysicalExtension period hPeriod configuration data analysis chart
        sameAction blocks).form test
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) =
      (sevenPhysicalExtension period hPeriod configuration data analysis chart
        sameAction blocks).form test state := by
  let physical := sevenPhysicalExtension period hPeriod configuration data
    analysis chart sameAction blocks
  rw [physical.symmetric test
      (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis state),
    physical.symmetric test state]
  exact congrArg (fun functional => functional test)
    (sevenPhysical_form_reduction_left period hPeriod configuration data analysis
      chart sameAction blocks state)

/-- Full seven-block physical Hessian restricted to the reduced completion. -/
def globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  (sevenPhysicalExtension period hPeriod configuration data analysis chart
    sameAction blocks).form.bilinearComp
      (globalCandidateAMinimalPhysicalReducedHilbertInclusion period hPeriod
        configuration data analysis)
      (globalCandidateAMinimalPhysicalReducedHilbertInclusion period hPeriod
        configuration data analysis)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_symmetric
    (first second : Reduced period hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian period
        hPeriod configuration data analysis chart sameAction blocks first second =
      globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian period
        hPeriod configuration data analysis chart sameAction blocks second first :=
  (sevenPhysicalExtension period hPeriod configuration data analysis chart
    sameAction blocks).symmetric _ _

/-- Strong Riesz representative of the reduced seven-block Hessian. -/
def globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis :=
  @InnerProductSpace.continuousLinearMapOfBilin
    Real
    (Reduced period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance inferInstance
    (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian period
      hPeriod configuration data analysis chart sameAction blocks)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_pairing
    (first second : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator
          period hPeriod configuration data analysis chart sameAction blocks first)
        second =
      globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian period
        hPeriod configuration data analysis chart sameAction blocks first second := by
  exact @InnerProductSpace.continuousLinearMapOfBilin_apply
    Real
    (Reduced period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance inferInstance
    (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian period
      hPeriod configuration data analysis chart sameAction blocks)
    first second

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_core
    (first second : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian period
        hPeriod configuration data analysis chart sameAction blocks
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk second)) =
      diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second := by
  rw [globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk,
    globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
  change
    (sevenPhysicalExtension period hPeriod configuration data analysis chart
      sameAction blocks).form
      (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis
        (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis first))
      (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis
        (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis second)) = _
  rw [sevenPhysical_form_reduction_left period hPeriod configuration data analysis
      chart sameAction blocks,
    sevenPhysical_form_reduction_right period hPeriod configuration data analysis
      chart sameAction blocks]
  change
    (sevenPhysicalExtension period hPeriod configuration data analysis chart
      sameAction blocks).form
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis first)
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis second) = _
  exact (sevenPhysicalExtension period hPeriod configuration data analysis chart
    sameAction blocks).smooth_agreement first second

/-- Base-point quadratic energy of all seven physical Hessian blocks. -/
def globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction :
    Reduced period hPeriod configuration data analysis → Real :=
  fun state => (1 / 2 : Real) *
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian period
      hPeriod configuration data analysis chart sameAction blocks state state

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_contDiff :
    ContDiff Real ⊤
      (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction
        period hPeriod configuration data analysis chart sameAction blocks) := by
  unfold globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction
  exact contDiff_const.mul
    ((globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian period
      hPeriod configuration data analysis chart sameAction blocks
      ).contDiff.clm_apply contDiff_id)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction
        period hPeriod configuration data analysis chart sameAction blocks) :=
  (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_contDiff
    period hPeriod configuration data analysis chart sameAction blocks).of_le
      (by simp)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_fderiv
    (state : Reduced period hPeriod configuration data analysis) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction
          period hPeriod configuration data analysis chart sameAction blocks)
        state =
      globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian period
        hPeriod configuration data analysis chart sameAction blocks state := by
  exact (symmetricQuadratic_hasFDerivAt
    (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian period
      hPeriod configuration data analysis chart sameAction blocks)
    (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_symmetric
      period hPeriod configuration data analysis chart sameAction blocks)
    state).fderiv

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_gradient_pairing
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator
          period hPeriod configuration data analysis chart sameAction blocks state)
        test =
      fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction
          period hPeriod configuration data analysis chart sameAction blocks)
        state test := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_pairing,
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_fderiv]

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_core
    (core : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction
        period hPeriod configuration data analysis chart sameAction blocks
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      (1 / 2 : Real) *
        diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
          configuration data analysis chart sameAction.chartBridge core core := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction,
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_core]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction4D
end JanusFormal
