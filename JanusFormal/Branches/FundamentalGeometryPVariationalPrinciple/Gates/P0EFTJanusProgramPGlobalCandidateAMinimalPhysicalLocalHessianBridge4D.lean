import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D

/-!
# D10-free local Candidate-A Hessian bridge

The historical local bridge is retained for compatibility, but its source is
the D10-extended tangent.  This gate states the actual Hessian interface on
the nonduplicated D10-free physical tangent.  The diagonal graph comparison
then retains the seven physical action blocks and isolates only the exact
matter--LL same-action mismatch.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalLocalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D

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

/-- The corrected smooth physical tangent is a dense injective core of the
local action chart.  D10 and duplicate legacy nonminimal directions do not
occur in this interface. -/
structure ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalFieldConfiguration period hPeriod)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) where
  basePoint : chart.Model
  basePoint_mem : basePoint ∈ chart.family.domain
  baseConfiguration_fields :
    (chart.family.datumAt basePoint basePoint_mem).1 = configuration
  tangentAnalysis :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      chart.Model
  tangentAnalysis_injective : Function.Injective tangentAnalysis
  tangentAnalysis_denseRange : DenseRange tangentAnalysis

/-- Actual local Hessian on the corrected D10-free physical smooth core. -/
noncomputable def globalCandidateAMinimalPhysicalLocalHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalFieldConfiguration period hPeriod)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration chart)
    (first second :
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration) : Real :=
  globalCandidateALocalHessian period hPeriod chart bridge.basePoint
    (bridge.tangentAnalysis first) (bridge.tangentAnalysis second)

theorem globalCandidateAMinimalPhysicalLocalHessianOnCore_comm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalFieldConfiguration period hPeriod)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration chart)
    (first second :
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :
    globalCandidateAMinimalPhysicalLocalHessianOnCore period hPeriod
        configuration chart bridge first second =
      globalCandidateAMinimalPhysicalLocalHessianOnCore period hPeriod
        configuration chart bridge second first :=
  globalCandidateALocalHessian_symmetric period hPeriod chart
    bridge.basePoint bridge.basePoint_mem
    (bridge.tangentAnalysis first) (bridge.tangentAnalysis second)

/-- Pullback of the exact nine-block covariant Hessian to the corrected
diagonal smooth core. -/
def diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateAMinimalPhysicalLocalHessianOnCore period hPeriod
    configuration.physical chart bridge
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis first)
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis second)

theorem diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore_comm
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore
        period hPeriod configuration data analysis chart bridge first second =
      diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore
        period hPeriod configuration data analysis chart bridge second first :=
  globalCandidateAMinimalPhysicalLocalHessianOnCore_comm period hPeriod
    configuration.physical chart bridge _ _

/-- Seven physical blocks pulled back to the corrected diagonal core. -/
def diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateALocalPhysicalHessian period hPeriod chart bridge.basePoint
    (bridge.tangentAnalysis
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis first))
    (bridge.tangentAnalysis
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis second))

/-- Matter and LL covariant blocks pulled back to the corrected core. -/
def diagonalExtendedBulkMinimalPhysicalLocalMatterLLHessianOnCore
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateALocalMatterLLHessian period hPeriod chart bridge.basePoint
    (bridge.tangentAnalysis
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis first))
    (bridge.tangentAnalysis
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis second))

theorem diagonalExtendedBulkMinimalPhysicalLocalCovariantHessian_split
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore
        period hPeriod configuration data analysis chart bridge first second =
      diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
          period hPeriod configuration data analysis chart bridge first second +
        diagonalExtendedBulkMinimalPhysicalLocalMatterLLHessianOnCore
          period hPeriod configuration data analysis chart bridge first second := by
  unfold diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore
    globalCandidateAMinimalPhysicalLocalHessianOnCore
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
    diagonalExtendedBulkMinimalPhysicalLocalMatterLLHessianOnCore
  rw [globalCandidateALocalHessian_eq_physical_add_matterLL
    period hPeriod chart bridge.basePoint bridge.basePoint_mem]
  rfl

/-- The sole remaining graph mismatch after retaining the physical Hessian. -/
def diagonalExtendedBulkMinimalPhysicalLocalMatterLLMismatchOnCore
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  diagonalExtendedBulkMinimalPhysicalLocalMatterLLHessianOnCore period hPeriod
      configuration data analysis chart bridge first second -
    diagonalExtendedBulkMatterLLHessianOnCore period hPeriod
      configuration data analysis first second

/-- Gauge-fixed covariant Hessian on the corrected D10-free core. -/
def diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore period hPeriod
      configuration data analysis chart bridge first second +
    diagonalExtendedBulkGaugeFixingHessianOnCore period hPeriod
      configuration data analysis first second

/-- Correct graph target: the existing graph plus all retained physical
blocks, never a graph obtained by cancelling physical dynamics. -/
def diagonalExtendedBulkMinimalPhysicalLocalAugmentedGraphHessianOnCore
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration
      data analysis first second +
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
      configuration data analysis chart bridge first second

theorem diagonalExtendedBulkMinimalPhysicalLocalGaugeFixed_decomposition
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore
        period hPeriod configuration data analysis chart bridge first second =
      diagonalExtendedBulkMinimalPhysicalLocalAugmentedGraphHessianOnCore
          period hPeriod configuration data analysis chart bridge first second +
        diagonalExtendedBulkMinimalPhysicalLocalMatterLLMismatchOnCore
          period hPeriod configuration data analysis chart bridge first second := by
  unfold diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore
    diagonalExtendedBulkMinimalPhysicalLocalAugmentedGraphHessianOnCore
    diagonalExtendedBulkMinimalPhysicalLocalMatterLLMismatchOnCore
    diagonalExtendedBulkGraphHessianOnCore
    diagonalExtendedBulkMatterLLHessianOnCore
    diagonalExtendedBulkGaugeFixingHessianOnCore
  rw [diagonalExtendedBulkMinimalPhysicalLocalCovariantHessian_split]
  rw [diagonalExtendedBulkHessian_apply]
  simp only [diagonalExtendedBulkSmoothEmbedding_apply_core]
  ring

theorem diagonalExtendedBulkMinimalPhysicalLocalGaugeFixed_eq_augmented_iff
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore
        period hPeriod configuration data analysis chart bridge first second =
        diagonalExtendedBulkMinimalPhysicalLocalAugmentedGraphHessianOnCore
          period hPeriod configuration data analysis chart bridge first second ↔
      diagonalExtendedBulkMinimalPhysicalLocalMatterLLMismatchOnCore
        period hPeriod configuration data analysis chart bridge first second = 0 := by
  rw [diagonalExtendedBulkMinimalPhysicalLocalGaugeFixed_decomposition]
  constructor <;> intro h <;> linarith

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
end JanusFormal
