import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D

/-!
# Canonical H11 extension from a common Hilbert chart

The blockwise H11 interface is useful when each physical sector is estimated
separately.  There is a shorter route when the chosen local variational chart
is already continuously linearly equivalent to the unique diagonal graph
Hilbert completion.  In that case the actual seven-block local Hessian is a
bounded bilinear form on the chart model and can be transported directly.

This file constructs `GlobalCandidateASevenPhysicalCommonDomainExtension4D`
from that equivalence and its compatibility with the existing dense smooth
core.  No second completion or independently chosen physical form appears.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Filter MeasureTheory Set Topology
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D

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

private abbrev CommonHilbertChartSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) commonHilbertChartNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CommonHilbertChartSpace period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) commonHilbertChartInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CommonHilbertChartSpace period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) commonHilbertChartNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CommonHilbertChartSpace period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) commonHilbertChartModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CommonHilbertChartSpace period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The Hessian of the seven physical local action blocks is symmetric at every
admissible chart point. -/
theorem globalCandidateALocalPhysicalHessian_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain)
    (first second : chart.Model) :
    globalCandidateALocalPhysicalHessian period hPeriod chart point first second =
      globalCandidateALocalPhysicalHessian period hPeriod chart point second first := by
  let blocks := globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain) measure
  have hC2 : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt
      (chart.blocksC2Within point hPoint) chart.isOpen_domain hPoint
  unfold globalCandidateALocalPhysicalHessian
  exact action_gradient_helmholtz_at
    (fullCoupledPhysicalAction blocks) point
    (fullCoupledPhysicalAction_contDiffAt blocks point hC2) first second

/-- A local chart whose model is the same topological vector space as the
existing H11 completion.  Compatibility is imposed only on the already named
dense smooth core. -/
structure ProgramPGlobalMinimalPhysicalCommonHilbertChart4D
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
      period hPeriod configuration data analysis chart) where
  toChart : CommonHilbertChartSpace period hPeriod configuration data analysis
    ≃L[Real] chart.Model
  smooth_core_compatibility :
    ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      toChart
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) =
        sameAction.chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis core)

/-- Transport the actual seven-block chart Hessian to the pre-existing common
Hilbert completion. -/
def globalCandidateASevenPhysicalCommonDomainExtension_of_hilbertChart
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
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCommonDomainExtension4D period hPeriod
      configuration data analysis chart sameAction where
  form :=
    (globalCandidateALocalPhysicalHessian period hPeriod chart
      sameAction.chartBridge.basePoint).bilinearComp
        hilbertChart.toChart.toContinuousLinearMap
        hilbertChart.toChart.toContinuousLinearMap
  symmetric := by
    intro first second
    exact globalCandidateALocalPhysicalHessian_symmetric period hPeriod chart
      sameAction.chartBridge.basePoint sameAction.chartBridge.basePoint_mem
      (hilbertChart.toChart first) (hilbertChart.toChart second)
  smooth_agreement := by
    intro first second
    change
      globalCandidateALocalPhysicalHessian period hPeriod chart
          sameAction.chartBridge.basePoint
          (hilbertChart.toChart
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis first))
          (hilbertChart.toChart
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis second)) = _
    rw [hilbertChart.smooth_core_compatibility first,
      hilbertChart.smooth_core_compatibility second]
    rfl

/-- Direct H11 certificate when the local chart itself is the common Hilbert
chart. -/
theorem global_candidateA_h11_common_augmented_domain_gate_of_hilbertChart
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
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D period hPeriod
      configuration data analysis chart sameAction
        (globalCandidateASevenPhysicalCommonDomainExtension_of_hilbertChart
          period hPeriod configuration data analysis chart sameAction
            hilbertChart) :=
  global_candidateA_h11_common_augmented_domain_gate period hPeriod
    configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCommonDomainExtension_of_hilbertChart
        period hPeriod configuration data analysis chart sameAction hilbertChart)

end
end P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
end JanusFormal
