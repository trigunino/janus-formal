import Mathlib.Analysis.InnerProductSpace.Completion
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Pairing4D

/-!
# Intrinsic L2 completion of the full shared-metric core

The common positive pairing defines a pre-Hilbert norm on a genuinely
data-indexed copy of the smooth shared core.  Its uniform completion is the
honest Hilbert completion used below; no surjectivity onto an unrelated
ambient `L2` product is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Completion4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open Set Topology
open scoped InnerProductSpace
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricTangent4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Pairing4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- A genuinely parameter-tagged copy of the smooth common core. -/
@[ext]
structure GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  toCore :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
      period hPeriod analysis

/-- Forget only the parameter tag. -/
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreEquiv
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
        period hPeriod configuration data analysis ≃
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis where
  toFun := fun core ↦ core.toCore
  invFun := fun core ↦ ⟨core⟩
  left_inv core := by cases core; rfl
  right_inv _ := rfl

instance globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    AddCommGroup
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
        period hPeriod configuration data analysis) :=
  Equiv.addCommGroup
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreEquiv
      period hPeriod configuration data analysis)

instance globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
        period hPeriod configuration data analysis) :=
  Equiv.module Real
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreEquiv
      period hPeriod configuration data analysis)

/-- The tagged and untagged smooth cores are linearly equivalent. -/
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreLinearEquiv
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
        period hPeriod configuration data analysis ≃ₗ[Real]
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis where
  __ :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreEquiv
      period hPeriod configuration data analysis
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[implicit_reducible]
noncomputable def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreInnerCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    PreInnerProductSpace.Core Real
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
        period hPeriod configuration data analysis) := by
  refine
    { inner := fun first second ↦
        globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
          period hPeriod configuration data analysis first.toCore second.toCore
      conj_inner_symm := ?_
      re_inner_nonneg := ?_
      add_left := ?_
      smul_left := ?_ }
  · intro first second
    simpa using
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_symm
        period hPeriod configuration data analysis second.toCore first.toCore)
  · intro core
    simpa using
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_self_nonneg
        period hPeriod configuration data analysis core.toCore)
  · intro first second third
    change
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
          period hPeriod configuration data analysis
            (first.toCore + second.toCore) third.toCore =
        globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
            period hPeriod configuration data analysis first.toCore third.toCore +
          globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
            period hPeriod configuration data analysis second.toCore third.toCore
    exact
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_add_left
        period hPeriod configuration data analysis first.toCore second.toCore
          third.toCore
  · intro first second scalar
    change
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
          period hPeriod configuration data analysis (scalar • first.toCore)
            second.toCore =
        scalar *
          globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
            period hPeriod configuration data analysis first.toCore second.toCore
    exact
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_smul_left
        period hPeriod configuration data analysis scalar first.toCore second.toCore

@[implicit_reducible]
noncomputable def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2InnerCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace.Core Real
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
        period hPeriod configuration data analysis) :=
  { __ :=
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreInnerCore
        period hPeriod configuration data analysis
    definite := by
      intro core hZero
      change
        globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
          period hPeriod configuration data analysis core.toCore core.toCore = 0
        at hZero
      apply
        GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore.ext
      exact
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_self_eq_zero_iff
          period hPeriod configuration data analysis core.toCore).mp hZero }

noncomputable instance globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
        period hPeriod configuration data analysis) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd :=
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2InnerCore
        period hPeriod configuration data analysis)

noncomputable instance globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
        period hPeriod configuration data analysis) :=
  InnerProductSpace.ofCore
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreInnerCore
      period hPeriod configuration data analysis)

/-- Intrinsic Hilbert completion of the positive shared-metric smooth core. -/
abbrev GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Completion
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  UniformSpace.Completion
    (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
      period hPeriod configuration data analysis)

/-- Dense canonical inclusion, composed with the harmless parameter tag. -/
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis →ₗ[Real]
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Completion
        period hPeriod configuration data analysis :=
  (UniformSpace.Completion.toComplₗᵢ
      (𝕜 := Real)
      (E :=
        GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
          period hPeriod configuration data analysis)).toLinearMap.comp
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreLinearEquiv
      period hPeriod configuration data analysis).symm.toLinearMap

theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Function.Injective
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion
        period hPeriod configuration data analysis) :=
  (UniformSpace.Completion.toComplₗᵢ
      (𝕜 := Real)
      (E :=
        GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
          period hPeriod configuration data analysis)).injective.comp
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreLinearEquiv
      period hPeriod configuration data analysis).symm.injective

theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion_denseRange
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    DenseRange
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion
        period hPeriod configuration data analysis) := by
  change DenseRange
    (((↑) :
        GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
            period hPeriod configuration data analysis →
          GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Completion
            period hPeriod configuration data analysis) ∘
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreLinearEquiv
        period hPeriod configuration data analysis).symm)
  exact UniformSpace.Completion.denseRange_coe.comp
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreLinearEquiv
      period hPeriod configuration data analysis).symm.surjective.denseRange
    (UniformSpace.Completion.continuous_coe
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
        period hPeriod configuration data analysis))

/-- Completeness of the intrinsic uniform completion. -/
@[implicit_reducible]
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2CompletionCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Completion
        period hPeriod configuration data analysis) := by
  infer_instance

/-- The dense inclusion preserves the full common pairing exactly. -/
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion_inner
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    inner Real
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion
          period hPeriod configuration data analysis first)
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion
          period hPeriod configuration data analysis second) =
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        period hPeriod configuration data analysis first second := by
  change inner Real
      ((UniformSpace.Completion.toComplₗᵢ
        (𝕜 := Real)
        (E :=
          GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
            period hPeriod configuration data analysis))
        ((globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreLinearEquiv
          period hPeriod configuration data analysis).symm first))
      ((UniformSpace.Completion.toComplₗᵢ
        (𝕜 := Real)
        (E :=
          GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
            period hPeriod configuration data analysis))
        ((globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreLinearEquiv
          period hPeriod configuration data analysis).symm second)) = _
  exact
    (UniformSpace.Completion.toComplₗᵢ
      (𝕜 := Real)
      (E :=
        GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCore
          period hPeriod configuration data analysis)).inner_map_map
      ((globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreLinearEquiv
        period hPeriod configuration data analysis).symm first)
      ((globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2PreHilbertCoreLinearEquiv
        period hPeriod configuration data analysis).symm second)

end
end P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Completion4D
end JanusFormal
