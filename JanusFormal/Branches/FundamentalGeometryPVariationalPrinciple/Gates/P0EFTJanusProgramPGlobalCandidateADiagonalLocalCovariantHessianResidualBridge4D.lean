import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalLocalVariationalChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D

/-!
# Local Candidate-A diagonal graph/covariant Hessian residual bridge

The open-domain variational chart is connected to the already constructed
diagonal BRST/matter/LL smooth core.  At any admissible base point, its actual
ambient Hessian has the same exact graph-plus-residual decomposition as the
legacy whole-space chart.  No physical block is duplicated.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateADiagonalLocalCovariantHessianResidualBridge4D

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
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalAnalyticSpine4D
open P0EFTJanusProgramPGlobalHessianFrontier4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D

universe u

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
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- The genuine smooth tangent is a dense injective core of a local chart at
one admissible point representing the same physical configuration. -/
structure ProgramPGlobalLocalVariationalChartCoreBridge4D
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
    GlobalFieldTangent period hPeriod configuration →ₗ[Real] chart.Model
  tangentAnalysis_injective : Function.Injective tangentAnalysis
  tangentAnalysis_denseRange : DenseRange tangentAnalysis

/-- Actual local-chart Hessian pulled back to the genuine smooth global
tangent core. -/
noncomputable def globalCandidateALocalHessianOnSmoothGlobalCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalFieldConfiguration period hPeriod)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration chart)
    (first second : GlobalFieldTangent period hPeriod configuration) : Real :=
  globalCandidateALocalHessian period hPeriod chart bridge.basePoint
    (bridge.tangentAnalysis first) (bridge.tangentAnalysis second)

theorem globalCandidateALocalHessianOnSmoothGlobalCore_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalFieldConfiguration period hPeriod)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration chart)
    (first second : GlobalFieldTangent period hPeriod configuration) :
    globalCandidateALocalHessianOnSmoothGlobalCore period hPeriod
        configuration chart bridge first second =
      globalCandidateALocalHessianOnSmoothGlobalCore period hPeriod
        configuration chart bridge second first :=
  globalCandidateALocalHessian_symmetric period hPeriod chart
    bridge.basePoint bridge.basePoint_mem
    (bridge.tangentAnalysis first) (bridge.tangentAnalysis second)

/-- Every legacy whole-space core bridge is exactly a local-domain bridge
with domain `univ`. -/
def programPGlobalVariationalChartCoreBridge4DToLocal
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalFieldConfiguration period hPeriod}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration chart) :
    ProgramPGlobalLocalVariationalChartCoreBridge4D period hPeriod
      configuration
      (globalCandidateAVariationalChartToLocal period hPeriod chart) where
  basePoint := bridge.baseConfiguration
  basePoint_mem := Set.mem_univ _
  baseConfiguration_fields := bridge.baseConfiguration_fields
  tangentAnalysis := bridge.tangentAnalysis
  tangentAnalysis_injective := bridge.tangentAnalysis_injective
  tangentAnalysis_denseRange := bridge.tangentAnalysis_denseRange

theorem globalCandidateALocalHessianOnSmoothGlobalCore_toLocal_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalFieldConfiguration period hPeriod)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration chart)
    (first second : GlobalFieldTangent period hPeriod configuration) :
    globalCandidateALocalHessianOnSmoothGlobalCore period hPeriod
        configuration
        (globalCandidateAVariationalChartToLocal period hPeriod chart)
        (programPGlobalVariationalChartCoreBridge4DToLocal
          period hPeriod bridge) first second =
      globalCandidateAHessianOnSmoothGlobalCore period hPeriod
        configuration chart bridge first second := by
  unfold globalCandidateALocalHessianOnSmoothGlobalCore
    globalCandidateAHessianOnSmoothGlobalCore
  rw [globalCandidateAVariationalChart_toLocal_hessian_eq]
  rfl

/-- Local covariant Candidate-A Hessian on the completed diagonal smooth
core. -/
def diagonalExtendedBulkLocalCovariantHessianOnCore
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
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateALocalHessianOnSmoothGlobalCore period hPeriod
    configuration.physical chart bridge
    (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
      configuration data analysis first)
    (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
      configuration data analysis second)

theorem diagonalExtendedBulkLocalCovariantHessianOnCore_comm
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
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkLocalCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge second first :=
  globalCandidateALocalHessianOnSmoothGlobalCore_symmetric period hPeriod
    configuration.physical chart bridge
    (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
      configuration data analysis first)
    (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
      configuration data analysis second)

/-- Local covariant Hessian plus the two already closed BRST gauge-fixing
Hessians. -/
def diagonalExtendedBulkLocalGaugeFixedCovariantHessianOnCore
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
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  diagonalExtendedBulkLocalCovariantHessianOnCore period hPeriod
      configuration data analysis chart bridge first second +
    diagonalExtendedBulkGaugeFixingHessianOnCore period hPeriod
      configuration data analysis first second

theorem diagonalExtendedBulkLocalGaugeFixedCovariantHessianOnCore_comm
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
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalGaugeFixedCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkLocalGaugeFixedCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge second first := by
  unfold diagonalExtendedBulkLocalGaugeFixedCovariantHessianOnCore
  rw [diagonalExtendedBulkLocalCovariantHessianOnCore_comm,
    diagonalExtendedBulkGaugeFixingHessianOnCore_comm]

/-- The sole local-chart comparison residual after removing the already
closed matter and LL graph blocks. -/
def diagonalExtendedBulkLocalPhysicalHessianResidualOnCore
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
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  diagonalExtendedBulkLocalCovariantHessianOnCore period hPeriod
      configuration data analysis chart bridge first second -
    diagonalExtendedBulkMatterLLHessianOnCore period hPeriod
      configuration data analysis first second

theorem diagonalExtendedBulkLocalPhysicalHessianResidualOnCore_comm
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
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalPhysicalHessianResidualOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkLocalPhysicalHessianResidualOnCore period hPeriod
        configuration data analysis chart bridge second first := by
  unfold diagonalExtendedBulkLocalPhysicalHessianResidualOnCore
  rw [diagonalExtendedBulkLocalCovariantHessianOnCore_comm,
    diagonalExtendedBulkMatterLLHessianOnCore_comm]

/-- Exact local-chart comparison with the completed graph Hessian. -/
theorem diagonalExtendedBulkLocalGaugeFixedCovariantHessian_decomposition
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
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalGaugeFixedCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration
          data analysis first second +
        diagonalExtendedBulkLocalPhysicalHessianResidualOnCore period hPeriod
          configuration data analysis chart bridge first second := by
  unfold diagonalExtendedBulkLocalGaugeFixedCovariantHessianOnCore
    diagonalExtendedBulkGraphHessianOnCore
    diagonalExtendedBulkLocalPhysicalHessianResidualOnCore
    diagonalExtendedBulkMatterLLHessianOnCore
    diagonalExtendedBulkGaugeFixingHessianOnCore
  rw [diagonalExtendedBulkHessian_apply]
  simp only [diagonalExtendedBulkSmoothEmbedding_apply_core]
  ring

/-- The local graph/covariant equality is equivalent to vanishing of the
same single physical residual. -/
theorem diagonalExtendedBulkLocalGaugeFixedCovariantHessian_eq_graph_iff
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
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalGaugeFixedCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
        diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration
          data analysis first second ↔
      diagonalExtendedBulkLocalPhysicalHessianResidualOnCore period hPeriod
        configuration data analysis chart bridge first second = 0 := by
  rw [diagonalExtendedBulkLocalGaugeFixedCovariantHessian_decomposition]
  constructor <;> intro h <;> linarith

/-- On a legacy chart embedded by `U = univ`, the local covariant core
Hessian is definitionally the previous one. -/
theorem diagonalExtendedBulkLocalCovariantHessianOnCore_toLocal_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalCovariantHessianOnCore period hPeriod
        configuration data analysis
        (globalCandidateAVariationalChartToLocal period hPeriod chart)
        (programPGlobalVariationalChartCoreBridge4DToLocal
          period hPeriod bridge) first second =
      diagonalExtendedBulkCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second := by
  unfold diagonalExtendedBulkLocalCovariantHessianOnCore
    diagonalExtendedBulkCovariantHessianOnCore
  rw [globalCandidateALocalHessianOnSmoothGlobalCore_toLocal_eq]

theorem diagonalExtendedBulkLocalPhysicalHessianResidualOnCore_toLocal_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalPhysicalHessianResidualOnCore period hPeriod
        configuration data analysis
        (globalCandidateAVariationalChartToLocal period hPeriod chart)
        (programPGlobalVariationalChartCoreBridge4DToLocal
          period hPeriod bridge) first second =
      diagonalExtendedBulkPhysicalHessianResidualOnCore period hPeriod
        configuration data analysis chart bridge first second := by
  unfold diagonalExtendedBulkLocalPhysicalHessianResidualOnCore
    diagonalExtendedBulkPhysicalHessianResidualOnCore
  rw [diagonalExtendedBulkLocalCovariantHessianOnCore_toLocal_eq]

end

end P0EFTJanusProgramPGlobalCandidateADiagonalLocalCovariantHessianResidualBridge4D
end JanusFormal
