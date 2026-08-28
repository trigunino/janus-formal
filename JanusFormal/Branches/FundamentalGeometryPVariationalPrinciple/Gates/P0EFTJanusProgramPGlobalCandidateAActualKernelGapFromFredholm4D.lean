import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointClosedRangeKernelGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D

/-!
# Recover the actual-kernel gap from the classical Candidate-A H12 estimates

The historical H12 interface stores closed range and finite-dimensional kernel.
For the already proved self-adjoint augmented Candidate-A operator, those two
facts canonically produce a bounded inverse on `(ker H)ᗮ` and hence a positive
gap.  This adapter makes every old H12 certificate immediately usable by the
new actual-kernel Green and resolvent layers.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualKernelGapFromFredholm4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
open P0EFTJanusProgramPSelfAdjointClosedRangeKernelGap4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

/-- Canonical actual-kernel packet extracted from an old H12 estimate packet. -/
def globalCandidateAActualKernelGap_of_fredholmEstimates
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
    (estimates : GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period
      hPeriod configuration data analysis chart sameAction physical) :
    GlobalCandidateAActualKernelGap4D period hPeriod configuration data analysis
      chart sameAction physical where
  gapData := selfAdjointKernelComplementGapData_of_closedRange
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    estimates.range_closed estimates.kernel_finite
  ll_stationary := estimates.ll_stationary

/-- Every old H12 packet now gives the exact zero-mode complement and the local
resolvent for free. -/
def global_candidateA_fredholmEstimates_to_actualKernel_gate
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
    (estimates : GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period
      hPeriod configuration data analysis chart sameAction physical) :=
  let gap := globalCandidateAActualKernelGap_of_fredholmEstimates period hPeriod
    configuration data analysis chart sameAction physical estimates
  And.intro
    (global_candidateA_actual_kernel_complement_gate period hPeriod configuration
      data analysis chart sameAction physical gap)
    (global_candidateA_actual_kernel_resolvent_gate period hPeriod configuration
      data analysis chart sameAction physical gap)

end
end P0EFTJanusProgramPGlobalCandidateAActualKernelGapFromFredholm4D
end JanusFormal
