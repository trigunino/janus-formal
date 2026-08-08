import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedExponential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolventIdentity4D

/-!
# Exact exponential of the reduced Candidate-A Hessian

The exact reduced Candidate-A Hessian is a bounded self-adjoint operator on the
zero-mode complement.  Its Banach-algebra exponential

`U(t) = exp (-t H_red)`

therefore exists for all real `t`, forms an exact one-parameter group, is
self-adjoint for real time and commutes with the reduced Hessian.

This is the genuine bounded operator exponential.  No compactness or
nuclearity claim is made here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponential4D

set_option autoImplicit false
set_option maxHeartbeats 6800000
set_option synthInstance.maxHeartbeats 3400000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedOperator4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolventIdentity4D
open P0EFTJanusProgramPFiniteDefectReducedExponential4D

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

/-- Exact reduced Candidate-A exponential. -/
noncomputable def globalCandidateAAugmentedReducedExponential
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical)
    (time : Real) :=
  finiteDefectReducedExponential
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift.coerciveShift time

/-- Exact structural certificate for the Candidate-A reduced exponential. -/
structure GlobalCandidateAAugmentedReducedExponentialCertificate4D
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical) : Prop where
  zero : globalCandidateAAugmentedReducedExponential period hPeriod
      configuration data analysis chart sameAction physical shift 0 = 1
  add : ∀ firstTime secondTime,
    globalCandidateAAugmentedReducedExponential period hPeriod configuration
        data analysis chart sameAction physical shift (firstTime + secondTime) =
      globalCandidateAAugmentedReducedExponential period hPeriod configuration
          data analysis chart sameAction physical shift firstTime *
        globalCandidateAAugmentedReducedExponential period hPeriod configuration
          data analysis chart sameAction physical shift secondTime
  isUnit : ∀ time,
    IsUnit (globalCandidateAAugmentedReducedExponential period hPeriod
      configuration data analysis chart sameAction physical shift time)
  selfAdjoint : ∀ time,
    IsSelfAdjoint (globalCandidateAAugmentedReducedExponential period hPeriod
      configuration data analysis chart sameAction physical shift time)
  commutes : ∀ time,
    Commute
      (globalCandidateAAugmentedReducedOperator period hPeriod configuration data
        analysis chart sameAction physical shift)
      (globalCandidateAAugmentedReducedExponential period hPeriod configuration
        data analysis chart sameAction physical shift time)

/-- Construction of the Candidate-A reduced-exponential certificate. -/
def globalCandidateAAugmentedReducedExponentialCertificate
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical) :
    GlobalCandidateAAugmentedReducedExponentialCertificate4D period hPeriod
      configuration data analysis chart sameAction physical shift := by
  have hGate := finite_defect_reduced_exponential_gate
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    (globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    shift.coerciveShift
  exact
    { zero := finiteDefectReducedExponential_zero _ shift.coerciveShift
      add := hGate.1
      isUnit := hGate.2.1
      selfAdjoint := hGate.2.2.1
      commutes := hGate.2.2.2 }

/-- Public Candidate-A reduced-exponential gate. -/
theorem global_candidateA_augmented_reduced_exponential_gate
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical) :
    GlobalCandidateAAugmentedReducedExponentialCertificate4D period hPeriod
      configuration data analysis chart sameAction physical shift :=
  globalCandidateAAugmentedReducedExponentialCertificate period hPeriod
    configuration data analysis chart sameAction physical shift

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedReducedExponential4D
end JanusFormal
