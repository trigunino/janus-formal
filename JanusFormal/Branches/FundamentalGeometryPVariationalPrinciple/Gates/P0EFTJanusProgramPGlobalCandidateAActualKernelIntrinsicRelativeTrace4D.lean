import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualKernelRelativeTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementIntrinsicRelativeTrace4D

/-!
# Intrinsic relative heat trace on the actual Candidate-A kernel complement

This file specializes presentation-independent nuclear trace data to the
genuine Candidate-A Hessian and its canonical zero-mode complement.  At every
positive time, all certified summable rank-one presentations of

`exp (-t H_red) - exp (-t H_ref)`

produce the same scalar.  The resulting trace is therefore the canonical input
to the preferred finite-part, Mellin, zeta and Quillen route.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualKernelIntrinsicRelativeTrace4D

set_option autoImplicit false
set_option maxHeartbeats 6800000
set_option synthInstance.maxHeartbeats 3400000

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
open P0EFTJanusProgramPGlobalCandidateAActualKernelRelativeTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPSelfAdjointKernelComplementIntrinsicRelativeTrace4D
open P0EFTJanusProgramPSelfAdjointKernelComplementRelativeHeat4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
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

/-- Candidate-A spelling of the intrinsic relative trace packet. -/
abbrev GlobalCandidateAActualKernelIntrinsicRelativeTraceData4D
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
  SelfAdjointKernelComplementIntrinsicRelativeTraceData
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)

/-- Canonical Candidate-A relative heat trace. -/
def globalCandidateAActualKernelIntrinsicRelativeHeatTrace
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
    (relative : GlobalCandidateAActualKernelIntrinsicRelativeTraceData4D period
      hPeriod configuration data analysis chart sameAction physical)
    (time : HeatTime) : Real :=
  selfAdjointKernelComplementIntrinsicRelativeHeatTrace
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    relative time

/-- Forget trace uniqueness while retaining one presentation-level Candidate-A
relative trace packet. -/
def GlobalCandidateAActualKernelIntrinsicRelativeTraceData4D.toRelativeTraceData
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
    (relative : GlobalCandidateAActualKernelIntrinsicRelativeTraceData4D period
      hPeriod configuration data analysis chart sameAction physical) :
    GlobalCandidateAActualKernelRelativeTraceData4D period hPeriod
      configuration data analysis chart sameAction physical :=
  SelfAdjointKernelComplementIntrinsicRelativeTraceData.toRelativeTraceData
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    relative

/-- Forgetting uniqueness leaves the same scalar relative heat trace. -/
theorem globalCandidateAActualKernelRelativeHeatTrace_toRelativeTraceData
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
    (relative : GlobalCandidateAActualKernelIntrinsicRelativeTraceData4D period
      hPeriod configuration data analysis chart sameAction physical)
    (time : HeatTime) :
    globalCandidateAActualKernelRelativeHeatTrace period hPeriod configuration
        data analysis chart sameAction physical
        (relative.toRelativeTraceData period hPeriod) time =
      globalCandidateAActualKernelIntrinsicRelativeHeatTrace period hPeriod
        configuration data analysis chart sameAction physical relative time :=
  rfl

/-- Every certified rank-one presentation computes the intrinsic Candidate-A
trace. -/
theorem globalCandidateAActualKernelIntrinsicRelativeHeatTrace_expansion_eq
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
    (relative : GlobalCandidateAActualKernelIntrinsicRelativeTraceData4D period
      hPeriod configuration data analysis chart sameAction physical)
    (time : HeatTime)
    (expansion : SummableRankOneOperatorExpansion
      (selfAdjointKernelComplementRelativeHeatDifference
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical)
        (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
          configuration data analysis chart sameAction physical)
        relative.referenceOperator time)) :
    expansion.expansionTrace =
      globalCandidateAActualKernelIntrinsicRelativeHeatTrace period hPeriod
        configuration data analysis chart sameAction physical relative time :=
  relative.expansionTrace_eq
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    time expansion

/-- Public intrinsic Candidate-A actual-kernel trace checkpoint. -/
theorem global_candidateA_actual_kernel_intrinsic_relative_trace_gate
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
    (relative : GlobalCandidateAActualKernelIntrinsicRelativeTraceData4D period
      hPeriod configuration data analysis chart sameAction physical) :
    (∀ time : HeatTime,
      IsCompactOperator
        (selfAdjointKernelComplementRelativeHeatDifference
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical)
          (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
            configuration data analysis chart sameAction physical)
          relative.referenceOperator time)) ∧
      (∀ time : HeatTime,
        ∀ expansion : SummableRankOneOperatorExpansion
          (selfAdjointKernelComplementRelativeHeatDifference
            (globalCandidateAActualKernelOperator period hPeriod configuration
              data analysis chart sameAction physical)
            (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
              configuration data analysis chart sameAction physical)
            relative.referenceOperator time),
          expansion.expansionTrace =
            globalCandidateAActualKernelIntrinsicRelativeHeatTrace period hPeriod
              configuration data analysis chart sameAction physical relative
                time) :=
  self_adjoint_kernel_complement_intrinsic_relative_trace_gate
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    relative

end
end P0EFTJanusProgramPGlobalCandidateAActualKernelIntrinsicRelativeTrace4D
end JanusFormal
