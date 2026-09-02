import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# A graph-adapted norm on the full minimal physical tangent

The minimal physical tangent is an algebraic real vector space.  A Hamel basis
embeds it injectively into an `ℓ¹` space.  Adjoining the canonical matter and LL
graph maps to that embedding induces a compatible norm for which both graph
maps have operator bound one.

This is an explicit noncanonical analytic choice, not a claim that the induced
topology is the geometric Sobolev topology.  It removes the abstract norm and
boundedness obligations from the minimal-chart frontier without supplying the
still-missing physical local action family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLGraphAdaptedNorm4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev MinimalModel
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

private local instance minimalModelAddCommGroup
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    AddCommGroup (MinimalModel period hPeriod configuration) :=
  Submodule.addCommGroup (MinimalModel period hPeriod configuration)

private local instance minimalModelModule
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Module Real (MinimalModel period hPeriod configuration) :=
  Submodule.module (MinimalModel period hPeriod configuration)

private noncomputable local instance minimalModelFree
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Module.Free Real (MinimalModel period hPeriod configuration) :=
  Module.Free.of_divisionRing Real
    (MinimalModel period hPeriod configuration)

private abbrev MinimalHamelIndex
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  Module.Free.ChooseBasisIndex Real
    (MinimalModel period hPeriod configuration)

private abbrev MinimalHamelL1
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  lp (fun _ : MinimalHamelIndex period hPeriod configuration => Real) 1

private noncomputable local instance graphAdaptedLLNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (globalFullLLGraphInnerProductSpace period hPeriod data analysis).toNormedSpace

private local instance (priority := 10000) graphAdaptedLLModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (graphAdaptedLLNormedSpace period hPeriod configuration data analysis).toModule

/-- A choice-dependent injective `ℓ¹` realization of the entire algebraic
minimal physical tangent. -/
def globalMinimalPhysicalHamelL1LinearMap
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    MinimalModel period hPeriod configuration →ₗ[Real]
      MinimalHamelL1 period hPeriod configuration :=
  (lp.linearMapOfLE Real
      (fun _ : MinimalHamelIndex period hPeriod configuration => Real)
      (p := 0) (q := 1) (by norm_num)).comp
    ((lp.zeroBasis
        (𝕜 := Real)
        (α := MinimalHamelIndex period hPeriod configuration)).repr.symm.toLinearMap.comp
      (Module.Free.chooseBasis Real
        (MinimalModel period hPeriod configuration)).repr.toLinearMap)

theorem globalMinimalPhysicalHamelL1LinearMap_injective
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Function.Injective
      (globalMinimalPhysicalHamelL1LinearMap period hPeriod configuration) := by
  intro first second hEqual
  apply
    (Module.Free.chooseBasis Real
      (MinimalModel period hPeriod configuration)).repr.injective
  apply
    (lp.zeroBasis
      (𝕜 := Real)
      (α := MinimalHamelIndex period hPeriod configuration)).repr.symm.injective
  apply Subtype.ext
  simpa [globalMinimalPhysicalHamelL1LinearMap] using
    congrArg
      (fun state : MinimalHamelL1 period hPeriod configuration => state.1)
      hEqual

private abbrev GraphAdaptedTarget
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  MinimalHamelL1 period hPeriod configuration ×
    (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared ×
      GlobalFullLLGraphHilbert period hPeriod data analysis)

/-- Injective graph embedding used to pull back the product norm. -/
def globalMinimalPhysicalMatterLLGraphEmbedding
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) :
    MinimalModel period hPeriod configuration →ₗ[Real]
      GraphAdaptedTarget period hPeriod configuration data analysis where
  toFun direction :=
    (globalMinimalPhysicalHamelL1LinearMap period hPeriod configuration direction,
      (globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
          couplings.matterMassSquared realization direction,
        globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction))
  map_add' first second := by simp
  map_smul' scalar direction := by simp

theorem globalMinimalPhysicalMatterLLGraphEmbedding_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) :
    Function.Injective
      (globalMinimalPhysicalMatterLLGraphEmbedding period hPeriod configuration
        data analysis realization) := by
  intro first second hEqual
  apply globalMinimalPhysicalHamelL1LinearMap_injective period hPeriod configuration
  exact congrArg Prod.fst hEqual

/-- Pullback of the product graph norm to the original minimal tangent. -/
@[reducible] def globalMinimalPhysicalMatterLLGraphNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) :
    NormedAddCommGroup (MinimalModel period hPeriod configuration) :=
  NormedAddCommGroup.induced
    (MinimalModel period hPeriod configuration)
    (GraphAdaptedTarget period hPeriod configuration data analysis)
    (globalMinimalPhysicalMatterLLGraphEmbedding period hPeriod configuration
      data analysis realization)
    (globalMinimalPhysicalMatterLLGraphEmbedding_injective period hPeriod
      configuration data analysis realization)

/-- The induced norm respects the original real scalar action. -/
@[reducible] def globalMinimalPhysicalMatterLLGraphNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) :
    letI : NormedAddCommGroup (MinimalModel period hPeriod configuration) :=
      globalMinimalPhysicalMatterLLGraphNormedAddCommGroup period hPeriod
        configuration data analysis realization
    NormedSpace Real (MinimalModel period hPeriod configuration) := by
  letI : NormedAddCommGroup (MinimalModel period hPeriod configuration) :=
    globalMinimalPhysicalMatterLLGraphNormedAddCommGroup period hPeriod
      configuration data analysis realization
  exact
    NormedSpace.induced Real
      (MinimalModel period hPeriod configuration)
      (GraphAdaptedTarget period hPeriod configuration data analysis)
      (globalMinimalPhysicalMatterLLGraphEmbedding period hPeriod configuration
        data analysis realization)

/-- The graph-adapted norm supplies both previously abstract bounds, with
constant one. -/
def globalMinimalPhysicalMatterLLGraphAdaptedBounds
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) :
    letI : NormedAddCommGroup (MinimalModel period hPeriod configuration) :=
      globalMinimalPhysicalMatterLLGraphNormedAddCommGroup period hPeriod
        configuration data analysis realization
    letI : NormedSpace Real (MinimalModel period hPeriod configuration) :=
      globalMinimalPhysicalMatterLLGraphNormedSpace period hPeriod configuration
        data analysis realization
    GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod configuration data
      analysis realization := by
  letI : NormedAddCommGroup (MinimalModel period hPeriod configuration) :=
    globalMinimalPhysicalMatterLLGraphNormedAddCommGroup period hPeriod
      configuration data analysis realization
  letI : NormedSpace Real (MinimalModel period hPeriod configuration) :=
    globalMinimalPhysicalMatterLLGraphNormedSpace period hPeriod configuration
      data analysis realization
  refine
    { toAddCommGroup_eq := rfl
      toSMul_eq := rfl
      matterBound := 1
      matter_le := ?_
      llBound := 1
      ll_le := ?_ }
  · intro direction
    rw [one_mul]
    change
      ‖globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
          couplings.matterMassSquared realization direction‖ ≤
        ‖globalMinimalPhysicalMatterLLGraphEmbedding period hPeriod configuration
          data analysis realization direction‖
    exact
      (norm_fst_le
        (globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
            couplings.matterMassSquared realization direction,
          globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
            data analysis direction)).trans
        (norm_snd_le
          (globalMinimalPhysicalMatterLLGraphEmbedding period hPeriod
            configuration data analysis realization direction))
  · intro direction
    rw [one_mul]
    change
      ‖globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction‖ ≤
        ‖globalMinimalPhysicalMatterLLGraphEmbedding period hPeriod configuration
          data analysis realization direction‖
    exact
      (norm_snd_le
        (globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
            couplings.matterMassSquared realization direction,
          globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration
            data analysis direction)).trans
        (norm_snd_le
          (globalMinimalPhysicalMatterLLGraphEmbedding period hPeriod
            configuration data analysis realization direction))

/-- Gate marker: the full minimal tangent always admits a compatible norm for
which the canonical matter and LL graph projections are continuous. -/
theorem global_candidateA_minimal_physical_matter_LL_graph_adapted_norm_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) :
    letI : NormedAddCommGroup (MinimalModel period hPeriod configuration) :=
      globalMinimalPhysicalMatterLLGraphNormedAddCommGroup period hPeriod
        configuration data analysis realization
    letI : NormedSpace Real (MinimalModel period hPeriod configuration) :=
      globalMinimalPhysicalMatterLLGraphNormedSpace period hPeriod configuration
        data analysis realization
    Nonempty
      (GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod configuration
        data analysis realization) := by
  letI : NormedAddCommGroup (MinimalModel period hPeriod configuration) :=
    globalMinimalPhysicalMatterLLGraphNormedAddCommGroup period hPeriod
      configuration data analysis realization
  letI : NormedSpace Real (MinimalModel period hPeriod configuration) :=
    globalMinimalPhysicalMatterLLGraphNormedSpace period hPeriod configuration
      data analysis realization
  exact
    ⟨globalMinimalPhysicalMatterLLGraphAdaptedBounds period hPeriod configuration
      data analysis realization⟩

end

end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLGraphAdaptedNorm4D
end JanusFormal
