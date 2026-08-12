import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementExponential4D

/-!
# Exact Candidate-A exponential on the genuine zero-mode complement

The augmented Candidate-A Hessian is bounded and self-adjoint on the unchanged
D10-free Hilbert space.  Its canonical restriction to the orthogonal complement
of the genuine kernel therefore has the exact exponential

`U(t) = exp (-t H_red)`.

Unlike the earlier finite-defect construction, this definition requires no
chosen defect projection or coercive shift.  It is attached directly to the
actual kernel complement used by the preferred five-sector H12 route.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualKernelExponential4D

set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option synthInstance.maxHeartbeats 2800000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPSelfAdjointKernelComplementExponential4D
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

/-- Exact exponential of the Candidate-A Hessian on `(ker H)ᗮ`. -/
noncomputable def globalCandidateAActualKernelExponential
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
    (time : Real) :=
  selfAdjointKernelComplementExponential
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    time

/-- Candidate-A structural exponential certificate. -/
structure GlobalCandidateAActualKernelExponentialCertificate4D
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
      hPeriod configuration data analysis chart sameAction) : Prop where
  zero : globalCandidateAActualKernelExponential period hPeriod configuration
      data analysis chart sameAction physical 0 = 1
  add : ∀ firstTime secondTime,
    globalCandidateAActualKernelExponential period hPeriod configuration data
        analysis chart sameAction physical (firstTime + secondTime) =
      globalCandidateAActualKernelExponential period hPeriod configuration data
          analysis chart sameAction physical firstTime *
        globalCandidateAActualKernelExponential period hPeriod configuration data
          analysis chart sameAction physical secondTime
  isUnit : ∀ time,
    IsUnit (globalCandidateAActualKernelExponential period hPeriod configuration
      data analysis chart sameAction physical time)
  selfAdjoint : ∀ time,
    IsSelfAdjoint (globalCandidateAActualKernelExponential period hPeriod
      configuration data analysis chart sameAction physical time)
  commutes : ∀ time,
    Commute
      (globalCandidateAActualKernelComplementOperator period hPeriod
        configuration data analysis chart sameAction physical)
      (globalCandidateAActualKernelExponential period hPeriod configuration data
        analysis chart sameAction physical time)

/-- Construct the exact Candidate-A exponential certificate. -/
def globalCandidateAActualKernelExponentialCertificate
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
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateAActualKernelExponentialCertificate4D period hPeriod
      configuration data analysis chart sameAction physical := by
  let generic := selfAdjointKernelComplementExponentialCertificate
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
  exact
    { zero := generic.zero
      add := generic.add
      isUnit := generic.isUnit
      selfAdjoint := generic.selfAdjoint
      commutes := generic.commutes }

/-- Public Candidate-A actual-kernel exponential gate. -/
theorem global_candidateA_actual_kernel_exponential_gate
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
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateAActualKernelExponentialCertificate4D period hPeriod
      configuration data analysis chart sameAction physical :=
  globalCandidateAActualKernelExponentialCertificate period hPeriod
    configuration data analysis chart sameAction physical

end
end P0EFTJanusProgramPGlobalCandidateAActualKernelExponential4D
end JanusFormal
