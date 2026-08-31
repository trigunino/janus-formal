import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D

/-!
# Canonical Hilbert completion of the reduced minimal physical smooth core

Gate 185 makes the quotient smooth-core embedding injective.  Its induced
Hilbert norm therefore has a canonical completion, and density identifies that
completion isometrically with the reduced physical Hilbert space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedSmoothCoreHilbertCompletion4D

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D

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

local instance completionCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance completionCommonInnerProductSpace : InnerProductSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance completionCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (completionCommonInnerProductSpace period hPeriod configuration data
    analysis).toNormedSpace

local instance completionCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (completionCommonNormedSpace period hPeriod configuration data
    analysis).toModule

local instance completionCommonCompleteSpace : CompleteSpace
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The algebraic reduced smooth core equipped below with its canonical
reduced-Hilbert norm. -/
abbrev GlobalCandidateAMinimalPhysicalReducedHilbertCore :=
  GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
    configuration data analysis

/-- Canonical analysis map from the quotient smooth core into the reduced
physical Hilbert space. -/
def globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis :
    GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
        configuration data analysis →ₗ[Real]
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis :=
  globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding period
    hPeriod configuration data analysis

theorem globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis_injective :
    Function.Injective
      (globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis period hPeriod
        configuration data analysis) :=
  globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_injective
    period hPeriod configuration data analysis

noncomputable instance reducedHilbertCoreNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
        configuration data analysis) :=
  NormedAddCommGroup.induced
    (GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
      configuration data analysis)
    (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis period hPeriod
      configuration data analysis)
    (globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis_injective
      period hPeriod configuration data analysis)

noncomputable instance reducedHilbertCoreNormedSpace :
    NormedSpace Real
      (GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
        configuration data analysis) :=
  NormedSpace.induced Real
    (GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
      configuration data analysis)
    (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis period hPeriod
      configuration data analysis)

noncomputable instance reducedHilbertCoreInnerProductSpace :
    InnerProductSpace Real
      (GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
        configuration data analysis) :=
  InnerProductSpace.induced
    (globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis period hPeriod
      configuration data analysis)

@[simp]
theorem globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis_norm
    (core : GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
      configuration data analysis) :
    ‖globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis period hPeriod
        configuration data analysis core‖ = ‖core‖ :=
  rfl

/-- The quotient smooth core is an isometric dense subspace of the reduced
physical Hilbert space. -/
def globalCandidateAMinimalPhysicalReducedHilbertCoreIsometry :
    GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
        configuration data analysis →ₗᵢ[Real]
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis where
  toLinearMap :=
    globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis period hPeriod
      configuration data analysis
  norm_map' :=
    globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis_norm period
      hPeriod configuration data analysis

theorem globalCandidateAMinimalPhysicalReducedHilbertCoreIsometry_denseRange :
    DenseRange
      (globalCandidateAMinimalPhysicalReducedHilbertCoreIsometry period hPeriod
        configuration data analysis) :=
  globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_denseRange
    period hPeriod configuration data analysis

/-- Completion of the reduced smooth quotient core in its intrinsic reduced
Hilbert norm. -/
abbrev GlobalCandidateAMinimalPhysicalReducedSmoothCoreHilbertCompletion :=
  UniformSpace.Completion
    (GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
      configuration data analysis)

/-- Canonical isometric inclusion of the reduced smooth core into its
completion. -/
def globalCandidateAMinimalPhysicalReducedHilbertCoreInclusion :
    GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
        configuration data analysis →ₗ[Real]
      GlobalCandidateAMinimalPhysicalReducedSmoothCoreHilbertCompletion period
        hPeriod configuration data analysis :=
  (UniformSpace.Completion.toComplₗᵢ
    (𝕜 := Real)
    (E := GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
      configuration data analysis)).toLinearMap

/-- The abstract completion of the quotient smooth core is canonically
unitary to the reduced physical Hilbert space. -/
def globalCandidateAMinimalPhysicalReducedSmoothCoreHilbertCompletionEquiv :
    GlobalCandidateAMinimalPhysicalReducedSmoothCoreHilbertCompletion period
        hPeriod configuration data analysis ≃ₗᵢ[Real]
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis :=
  LinearEquiv.extendOfIsometry
    (E := GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
      configuration data analysis)
    (F := GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
      configuration data analysis)
    (LinearEquiv.refl Real
      (GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
        configuration data analysis))
    (globalCandidateAMinimalPhysicalReducedHilbertCoreInclusion period hPeriod
      configuration data analysis)
    (globalCandidateAMinimalPhysicalReducedHilbertCoreIsometry period hPeriod
      configuration data analysis).toLinearMap
    UniformSpace.Completion.denseRange_coe
    (globalCandidateAMinimalPhysicalReducedHilbertCoreIsometry_denseRange
      period hPeriod configuration data analysis)
    (by
      intro core
      change
        ‖globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis period hPeriod
            configuration data analysis core‖ =
          ‖(core :
            GlobalCandidateAMinimalPhysicalReducedSmoothCoreHilbertCompletion
              period hPeriod configuration data analysis)‖
      rw [UniformSpace.Completion.norm_coe]
      exact
        globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis_norm period
          hPeriod configuration data analysis core)

@[simp]
theorem globalCandidateAMinimalPhysicalReducedSmoothCoreHilbertCompletionEquiv_core
    (core : GlobalCandidateAMinimalPhysicalReducedHilbertCore period hPeriod
      configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedSmoothCoreHilbertCompletionEquiv
        period hPeriod configuration data analysis
        (core :
          GlobalCandidateAMinimalPhysicalReducedSmoothCoreHilbertCompletion
            period hPeriod configuration data analysis) =
      globalCandidateAMinimalPhysicalReducedHilbertCoreAnalysis period hPeriod
        configuration data analysis core := by
  change
    globalCandidateAMinimalPhysicalReducedSmoothCoreHilbertCompletionEquiv
        period hPeriod configuration data analysis
        (globalCandidateAMinimalPhysicalReducedHilbertCoreInclusion period
          hPeriod configuration data analysis core) =
      (globalCandidateAMinimalPhysicalReducedHilbertCoreIsometry period hPeriod
        configuration data analysis).toLinearMap core
  unfold
    globalCandidateAMinimalPhysicalReducedSmoothCoreHilbertCompletionEquiv
  rw [LinearEquiv.extendOfIsometry_eq]
  rfl

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedSmoothCoreHilbertCompletion4D
end JanusFormal
