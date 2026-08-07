import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D

/-!
# Canonical graph projections from the minimal physical tangent

The minimal-physical chart still exposed arbitrary continuous projections to
the primitive matter graph and the full LL graph.  The LL projection is already
algebraically determined by the three LL slots and the existing smooth graph
embedding.  The matter projection is determined once smooth primitive SpinC
sections are realized in the maximal graph domain.

This file names that sole matter-domain realization and turns both algebraic
projections into bounded maps from one explicit pair of graph-norm estimates.
No new action or graph completion is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev MinimalProjectionModel
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

/-- Analytic realization of every genuine smooth two-sector primitive SpinC
field in the exact maximal graph domain.  Agreement on the finite Fourier core
prevents an unrelated extension, while action agreement records that this is
the same primitive matter action. -/
structure ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
    (massSquared : Real) where
  toGraph :
    ProgramPPrimitiveSpinCMatterSmoothField period hPeriod →ₗ[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared
  finite_compatibility :
    ∀ coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      toGraph
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            coefficients) =
        programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
          coefficients
  action_agreement :
    ∀ field : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod,
      programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          (toGraph field) =
        programPPrimitiveSpinCMatterSmoothAction period hPeriod massSquared
          field
  injective : Function.Injective toGraph

/-- Algebraic primitive-matter graph projection of a minimal physical tangent. -/
def globalMinimalPhysicalMatterGraphLinearMap
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (massSquared : Real)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod massSquared) :
    MinimalProjectionModel period hPeriod configuration →ₗ[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared :=
  realization.toGraph.comp
    (globalMinimalPhysicalSpinCMatterLinearMap period hPeriod configuration)

/-- Algebraic full-LL graph projection, using exactly the three LL slots of the
minimal physical tangent and the existing faithful smooth embedding. -/
def globalMinimalPhysicalLLGraphLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    MinimalProjectionModel period hPeriod configuration →ₗ[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
  (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis).comp
    (globalMinimalPhysicalFullLLSmoothLinearMap period hPeriod configuration
      analysis)

/-- The two graph-norm estimates required to make the canonical algebraic
projections continuous for the selected norm on the minimal physical chart. -/
structure GlobalMinimalPhysicalMatterLLGraphBounds4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [NormedAddCommGroup (MinimalProjectionModel period hPeriod configuration)]
    [NormedSpace Real (MinimalProjectionModel period hPeriod configuration)] where
  matterBound : Real
  matter_le : ∀ direction,
    ‖globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
        couplings.matterMassSquared realization direction‖ ≤
      matterBound * ‖direction‖
  llBound : Real
  ll_le : ∀ direction,
    ‖globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
        analysis direction‖ ≤ llBound * ‖direction‖

/-- Continuous primitive-matter graph projection obtained from its graph-norm
estimate. -/
def globalMinimalPhysicalMatterGraphCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [NormedAddCommGroup (MinimalProjectionModel period hPeriod configuration)]
    [NormedSpace Real (MinimalProjectionModel period hPeriod configuration)]
    (bounds : GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
      configuration data analysis realization) :
    MinimalProjectionModel period hPeriod configuration →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared :=
  (globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
    couplings.matterMassSquared realization).mkContinuous bounds.matterBound
      bounds.matter_le

/-- Continuous full-LL graph projection obtained from its graph-norm estimate. -/
def globalMinimalPhysicalLLGraphCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [NormedAddCommGroup (MinimalProjectionModel period hPeriod configuration)]
    [NormedSpace Real (MinimalProjectionModel period hPeriod configuration)]
    (bounds : GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
      configuration data analysis realization) :
    MinimalProjectionModel period hPeriod configuration →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
  (globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
    analysis).mkContinuous bounds.llBound bounds.ll_le

@[simp]
theorem globalMinimalPhysicalMatterGraphCLM_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [NormedAddCommGroup (MinimalProjectionModel period hPeriod configuration)]
    [NormedSpace Real (MinimalProjectionModel period hPeriod configuration)]
    (bounds : GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
      configuration data analysis realization)
    (direction : MinimalProjectionModel period hPeriod configuration) :
    globalMinimalPhysicalMatterGraphCLM period hPeriod configuration data
        analysis realization bounds direction =
      realization.toGraph direction.1.2 :=
  rfl

@[simp]
theorem globalMinimalPhysicalLLGraphCLM_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    [NormedAddCommGroup (MinimalProjectionModel period hPeriod configuration)]
    [NormedSpace Real (MinimalProjectionModel period hPeriod configuration)]
    (bounds : GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
      configuration data analysis realization)
    (direction : MinimalProjectionModel period hPeriod configuration) :
    globalMinimalPhysicalLLGraphCLM period hPeriod configuration data analysis
        realization bounds direction =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        (globalMinimalPhysicalFullLLSmoothLinearMap period hPeriod configuration
          analysis direction) :=
  rfl

/-- Compatibility of the canonical graph projections with the existing
finite/LL diagonal smooth core.  These equalities can normally be discharged
by unfolding the typed tangent assembly; they are kept together here as the
final algebraic adapter. -/
structure GlobalMinimalPhysicalMatterLLGraphCoreCompatibility4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) : Prop where
  matter : ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis,
    globalMinimalPhysicalMatterGraphLinearMap period hPeriod configuration
        couplings.matterMassSquared realization
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core) =
      programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
        couplings.matterMassSquared core.2.2.1
  ll : ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis,
    globalMinimalPhysicalLLGraphLinearMap period hPeriod configuration data
        analysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core) =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        core.2.2.2

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
end JanusFormal
