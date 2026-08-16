import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualKernelExponential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementRelativeTrace4D

/-!
# Relative heat trace on the actual Candidate-A kernel complement

This file gives the Candidate-A spelling of the relative trace packet built on
the genuine orthogonal complement of the actual Hessian kernel.  It replaces
the earlier finite-defect/shift presentation by the canonical reduced operator
used by the preferred five-sector route.

A summable rank-one expansion of

`exp (-t H_red) - exp (-t H_ref)`

produces compact relative heat and an absolutely summable scalar trace series.
Mellin continuation and representation independence remain explicit later
inputs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualKernelRelativeTrace4D

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 3100000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAActualKernelExponential4D
open P0EFTJanusProgramPSelfAdjointKernelComplementRelativeHeat4D
open P0EFTJanusProgramPSelfAdjointKernelComplementRelativeTrace4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Candidate-A actual-kernel relative trace packet. -/
abbrev GlobalCandidateAActualKernelRelativeTraceData4D
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :=
  SelfAdjointKernelComplementRelativeTraceData
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)

/-- Candidate-A scalar relative heat trace. -/
def globalCandidateAActualKernelRelativeHeatTrace
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (relative : GlobalCandidateAActualKernelRelativeTraceData4D period hPeriod
      configuration data analysis chart sameAction physical)
    (time : HeatTime) : Real :=
  selfAdjointKernelComplementRelativeHeatTrace
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    relative time

/-- Compact relative-heat packet obtained by forgetting the trace
presentation. -/
def GlobalCandidateAActualKernelRelativeTraceData4D.toRelativeHeatData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    (relative : GlobalCandidateAActualKernelRelativeTraceData4D period hPeriod
      configuration data analysis chart sameAction physical) :=
  SelfAdjointKernelComplementRelativeTraceData.toRelativeHeatData
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    relative

/-- The Candidate-A relative heat difference is compact. -/
theorem globalCandidateAActualKernelRelativeHeat_compact
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (relative : GlobalCandidateAActualKernelRelativeTraceData4D period hPeriod
      configuration data analysis chart sameAction physical)
    (time : HeatTime) :
    IsCompactOperator
      (selfAdjointKernelComplementRelativeHeatDifference
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical)
        (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
          configuration data analysis chart sameAction physical)
        relative.referenceOperator time) :=
  relative.relativeHeat_compact
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    time

/-- Candidate-A relative trace series is summable at every positive time. -/
theorem globalCandidateAActualKernelRelativeTrace_summable
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (relative : GlobalCandidateAActualKernelRelativeTraceData4D period hPeriod
      configuration data analysis chart sameAction physical)
    (time : HeatTime) :
    Summable (fun index =>
      (relative.relativeRankOneExpansion time).coefficient index *
        inner Real
          ((relative.relativeRankOneExpansion time).leftVector index)
          ((relative.relativeRankOneExpansion time).rightVector index)) :=
  relative.relativeTrace_summable
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    time

/-- Public Candidate-A actual-kernel relative-trace checkpoint. -/
theorem global_candidateA_actual_kernel_relative_trace_gate
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (relative : GlobalCandidateAActualKernelRelativeTraceData4D period hPeriod
      configuration data analysis chart sameAction physical) :
    (∀ time : HeatTime,
      IsCompactOperator
        (selfAdjointKernelComplementRelativeHeatDifference
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical)
          (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
            configuration data analysis chart sameAction physical)
          relative.referenceOperator time)) ∧
      (∀ time : HeatTime,
        Summable (fun index =>
          (relative.relativeRankOneExpansion time).coefficient index *
            inner Real
              ((relative.relativeRankOneExpansion time).leftVector index)
              ((relative.relativeRankOneExpansion time).rightVector index))) :=
  ⟨globalCandidateAActualKernelRelativeHeat_compact period hPeriod configuration
      data analysis chart sameAction physical relative,
    globalCandidateAActualKernelRelativeTrace_summable period hPeriod
      configuration data analysis chart sameAction physical relative⟩

end
end P0EFTJanusProgramPGlobalCandidateAActualKernelRelativeTrace4D
end JanusFormal
