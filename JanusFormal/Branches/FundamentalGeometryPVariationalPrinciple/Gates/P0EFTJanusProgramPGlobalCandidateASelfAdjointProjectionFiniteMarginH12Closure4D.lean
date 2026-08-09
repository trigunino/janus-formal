import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASelfAdjointProjectionFiniteMarginActualKernelGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAProjectionFiniteMarginH12Closure4D

/-!
# Candidate-A H12 closure from symmetric idempotent sector projections

The natural five projection laws generate the positive projection packet and
therefore the finite-margin actual-kernel gap.  This file exposes the direct H12
Fredholm, Green, resolvent and stability endpoints.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASelfAdjointProjectionFiniteMarginH12Closure4D

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

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
open P0EFTJanusProgramPGlobalCandidateASelfAdjointProjectionFiniteMarginActualKernelGap4D
open P0EFTJanusProgramPGlobalCandidateAProjectionFiniteMarginH12Closure4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D

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

/-- H12 and the complete reduced spectral package generated from the natural
five-sector projection laws. -/
def global_candidateA_selfAdjoint_projection_h12_closure_gate
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
    (natural : GlobalCandidateASelfAdjointProjectionFiniteMarginActualKernelGap4D
      period hPeriod configuration data analysis chart sameAction physical) :=
  global_candidateA_projection_finite_margin_h12_closure_gate period hPeriod
    configuration data analysis chart sameAction physical
      (natural.toProjection period hPeriod)

/-- Quantitative stability from the same natural projection laws. -/
def global_candidateA_selfAdjoint_projection_h12_stability_gate
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
    (natural : GlobalCandidateASelfAdjointProjectionFiniteMarginActualKernelGap4D
      period hPeriod configuration data analysis chart sameAction physical)
    (perturbation : GlobalCandidateAActualKernelPerturbation4D period hPeriod
      configuration data analysis chart sameAction physical
        (natural.toActualKernelGap period hPeriod)) :=
  global_candidateA_actual_kernel_stability_gate period hPeriod configuration
    data analysis chart sameAction physical
      (natural.toActualKernelGap period hPeriod) perturbation

end
end P0EFTJanusProgramPGlobalCandidateASelfAdjointProjectionFiniteMarginH12Closure4D
end JanusFormal
