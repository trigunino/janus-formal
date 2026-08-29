import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiniteMarginActualKernelGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D

/-!
# H12, reduced Green and resolvent from the finite Candidate-A margin

The five diagonal estimates, ten cross-form norms and one H11 physical bound
produce the actual-kernel gap.  The existing H12 machinery then supplies the
Fredholm certificate, index zero, reduced inverse, real resolvent and
perturbative stability.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiniteMarginH12Closure4D

set_option autoImplicit false
set_option maxHeartbeats 7600000
set_option synthInstance.maxHeartbeats 3800000

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
open P0EFTJanusProgramPGlobalCandidateAFiniteMarginActualKernelGap4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
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

/-- H12 and the complete reduced spectral package generated from the finite
coercive margin. -/
def global_candidateA_finite_margin_h12_closure_gate
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
    (finite : GlobalCandidateAFiniteMarginActualKernelGap4D period hPeriod
      configuration data analysis chart sameAction physical) :=
  let gap := finite.toActualKernelGap period hPeriod
  let fredholm := global_candidateA_h12_fredholm_gate_of_actualKernelGap
    period hPeriod configuration data analysis chart sameAction physical gap
  let complement := global_candidateA_actual_kernel_complement_gate period
    hPeriod configuration data analysis chart sameAction physical gap
  let resolvent := global_candidateA_actual_kernel_resolvent_gate period hPeriod
    configuration data analysis chart sameAction physical gap
  And.intro fredholm (And.intro complement resolvent)

/-- Quantitative stability generated from the same finite margin. -/
def global_candidateA_finite_margin_h12_stability_gate
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
    (finite : GlobalCandidateAFiniteMarginActualKernelGap4D period hPeriod
      configuration data analysis chart sameAction physical)
    (perturbation : GlobalCandidateAActualKernelPerturbation4D period hPeriod
      configuration data analysis chart sameAction physical
        (finite.toActualKernelGap period hPeriod)) :=
  global_candidateA_actual_kernel_stability_gate period hPeriod configuration
    data analysis chart sameAction physical
      (finite.toActualKernelGap period hPeriod) perturbation

end
end P0EFTJanusProgramPGlobalCandidateAFiniteMarginH12Closure4D
end JanusFormal
