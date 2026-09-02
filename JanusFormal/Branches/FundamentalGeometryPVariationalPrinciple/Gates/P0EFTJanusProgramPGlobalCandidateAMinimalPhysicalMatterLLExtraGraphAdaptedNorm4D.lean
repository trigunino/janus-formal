import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLGraphAdaptedNorm4D

/-!
# A graph-adapted norm with one additional algebraic projection

Any additional real-linear map can be included as one more graph coordinate.
The induced norm makes the matter, LL and additional projections continuous
with bound one.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLGraphAdaptedNorm4D

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

private noncomputable local instance extraGraphLLNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (globalFullLLGraphInnerProductSpace period hPeriod data analysis).toNormedSpace

private local instance (priority := 10000) extraGraphLLModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (extraGraphLLNormedSpace period hPeriod configuration data analysis).toModule

private abbrev ExtraGraphTarget
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  MinimalHamelL1 period hPeriod configuration ×
    (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared ×
      (GlobalFullLLGraphHilbert period hPeriod data analysis × W))

/-- Injective graph embedding with one arbitrary extra algebraic coordinate. -/
def globalMinimalPhysicalMatterLLExtraGraphEmbedding
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W) :
    MinimalModel period hPeriod configuration →ₗ[Real]
      ExtraGraphTarget period hPeriod (W := W) configuration data analysis where
  toFun direction :=
    (globalMinimalPhysicalHamelL1LinearMap period hPeriod configuration direction,
      (globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
          couplings.matterMassSquared realization direction,
        (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction, extra direction)))
  map_add' first second := by simp
  map_smul' scalar direction := by simp

theorem globalMinimalPhysicalMatterLLExtraGraphEmbedding_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W) :
    Function.Injective
      (globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
        configuration data analysis realization extra) := by
  intro first second hEqual
  apply globalMinimalPhysicalHamelL1LinearMap_injective period hPeriod
    configuration
  exact congrArg Prod.fst hEqual

@[reducible] def globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W) :
    NormedAddCommGroup (MinimalModel period hPeriod configuration) :=
  NormedAddCommGroup.induced
    (MinimalModel period hPeriod configuration)
    (ExtraGraphTarget period hPeriod (W := W) configuration data analysis)
    (globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
      configuration data analysis realization extra)
    (globalMinimalPhysicalMatterLLExtraGraphEmbedding_injective period hPeriod
      configuration data analysis realization extra)

@[reducible] def globalMinimalPhysicalMatterLLExtraGraphNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W) :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis realization extra
    NormedSpace Real (MinimalModel period hPeriod configuration) := by
  letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
    hPeriod configuration data analysis realization extra
  exact NormedSpace.induced Real (MinimalModel period hPeriod configuration)
    (ExtraGraphTarget period hPeriod (W := W) configuration data analysis)
    (globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
      configuration data analysis realization extra)

private theorem matter_norm_le
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W)
    (direction : MinimalModel period hPeriod configuration) :
    ‖globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
        couplings.matterMassSquared realization direction‖ ≤
      ‖globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
        configuration data analysis realization extra direction‖ :=
  (norm_fst_le
      (globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
          couplings.matterMassSquared realization direction,
        (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction, extra direction))).trans
    (norm_snd_le
      (globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
        configuration data analysis realization extra direction))

private theorem ll_norm_le
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W)
    (direction : MinimalModel period hPeriod configuration) :
    ‖globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
        analysis direction‖ ≤
      ‖globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
        configuration data analysis realization extra direction‖ :=
  ((norm_fst_le
      (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction, extra direction)).trans
    (norm_snd_le
      (globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
          couplings.matterMassSquared realization direction,
        (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction, extra direction)))).trans
    (norm_snd_le
      (globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
        configuration data analysis realization extra direction))

private theorem extra_norm_le
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W)
    (direction : MinimalModel period hPeriod configuration) :
    ‖extra direction‖ ≤
      ‖globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
        configuration data analysis realization extra direction‖ :=
  ((norm_snd_le
      (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction, extra direction)).trans
    (norm_snd_le
      (globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
          couplings.matterMassSquared realization direction,
        (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction, extra direction)))).trans
    (norm_snd_le
      (globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
        configuration data analysis realization extra direction))

/-- The matter graph projection as a contraction for the induced norm. -/
def globalMinimalPhysicalMatterLLExtraGraphMatterCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W) :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis realization extra
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
      configuration data analysis realization extra
    MinimalModel period hPeriod configuration →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared := by
  letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
    hPeriod configuration data analysis realization extra
  letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
    configuration data analysis realization extra
  exact (globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
    couplings.matterMassSquared realization).mkContinuous 1 (by
      intro direction
      rw [one_mul]
      change
        ‖globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
            couplings.matterMassSquared realization direction‖ ≤
          ‖globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
            configuration data analysis realization extra direction‖
      exact matter_norm_le period hPeriod configuration data analysis
        realization extra direction)

/-- The LL graph projection as a contraction for the induced norm. -/
def globalMinimalPhysicalMatterLLExtraGraphLLCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W) :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis realization extra
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
      configuration data analysis realization extra
    MinimalModel period hPeriod configuration →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis := by
  letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
    hPeriod configuration data analysis realization extra
  letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
    configuration data analysis realization extra
  exact (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
    analysis).mkContinuous 1 (by
      intro direction
      rw [one_mul]
      change
        ‖globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
            analysis direction‖ ≤
          ‖globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
            configuration data analysis realization extra direction‖
      exact ll_norm_le period hPeriod configuration data analysis realization
        extra direction)

/-- The arbitrary extra algebraic projection as a contraction. -/
def globalMinimalPhysicalMatterLLExtraGraphExtraCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W) :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis realization extra
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
      configuration data analysis realization extra
    MinimalModel period hPeriod configuration →L[Real] W := by
  letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
    hPeriod configuration data analysis realization extra
  letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
    configuration data analysis realization extra
  exact extra.mkContinuous 1 (by
    intro direction
    rw [one_mul]
    change ‖extra direction‖ ≤
      ‖globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
        configuration data analysis realization extra direction‖
    exact extra_norm_le period hPeriod configuration data analysis realization
      extra direction)

/-- The matter and LL estimates retained by the existing minimal-chart API. -/
def globalMinimalPhysicalMatterLLExtraGraphAdaptedBounds
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W) :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis realization extra
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
      configuration data analysis realization extra
    GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod configuration data
      analysis realization := by
  letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
    hPeriod configuration data analysis realization extra
  letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
    configuration data analysis realization extra
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
        ‖globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
          configuration data analysis realization extra direction‖
    exact matter_norm_le period hPeriod configuration data analysis realization
      extra direction
  · intro direction
    rw [one_mul]
    change
      ‖globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
          analysis direction‖ ≤
        ‖globalMinimalPhysicalMatterLLExtraGraphEmbedding period hPeriod
          configuration data analysis realization extra direction‖
    exact ll_norm_le period hPeriod configuration data analysis realization
      extra direction

/-- Gate 320: three graph coordinates are contractions for one induced norm. -/
theorem global_candidateA_minimal_physical_matter_LL_extra_graph_adapted_norm_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace W : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (extra : MinimalModel period hPeriod configuration →ₗ[Real] W) :
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period
      hPeriod configuration data analysis realization extra
    letI := globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
      configuration data analysis realization extra
    Nonempty
      ((MinimalModel period hPeriod configuration →L[Real]
          ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
            couplings.matterMassSquared) ×
        (MinimalModel period hPeriod configuration →L[Real]
          GlobalFullLLGraphHilbert period hPeriod data analysis) ×
        (MinimalModel period hPeriod configuration →L[Real] W)) := by
  exact ⟨(globalMinimalPhysicalMatterLLExtraGraphMatterCLM period hPeriod
      configuration data analysis realization extra,
    globalMinimalPhysicalMatterLLExtraGraphLLCLM period hPeriod configuration
      data analysis realization extra,
    globalMinimalPhysicalMatterLLExtraGraphExtraCLM period hPeriod configuration
      data analysis realization extra)⟩

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D
end JanusFormal
