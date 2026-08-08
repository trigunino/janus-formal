import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedResolventIdentity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolvent4D

/-!
# Candidate-A reduced resolvent identity

The real reduced Candidate-A resolvent satisfies the first resolvent identity
on the entire certified coercive interval.  The corresponding operator-norm
estimate makes the family quantitatively continuous away from the interval
endpoints.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolventIdentity4D

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolvent4D
open P0EFTJanusProgramPFiniteDefectReducedResolventIdentity4D

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

/-- First resolvent identity for the actual reduced Candidate-A Hessian. -/
theorem globalCandidateAAugmentedReducedRealResolvent_identity
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
    (firstParameter secondParameter : Real)
    (hFirst : |firstParameter| < shift.coerciveShift.coercivityConstant)
    (hSecond : |secondParameter| < shift.coerciveShift.coercivityConstant) :
    globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
        data analysis chart sameAction physical shift firstParameter hFirst -
      globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
        data analysis chart sameAction physical shift secondParameter hSecond =
      (firstParameter - secondParameter) •
        ((globalCandidateAAugmentedReducedRealResolvent period hPeriod
            configuration data analysis chart sameAction physical shift
            firstParameter hFirst).comp
          (globalCandidateAAugmentedReducedRealResolvent period hPeriod
            configuration data analysis chart sameAction physical shift
            secondParameter hSecond)) :=
  finiteDefectReducedRealResolvent_identity
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    (globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    shift.coerciveShift firstParameter secondParameter hFirst hSecond

/-- Quantitative operator-norm continuity of the Candidate-A resolvent. -/
theorem globalCandidateAAugmentedReducedRealResolvent_sub_opNorm_le
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
    (firstParameter secondParameter : Real)
    (hFirst : |firstParameter| < shift.coerciveShift.coercivityConstant)
    (hSecond : |secondParameter| < shift.coerciveShift.coercivityConstant) :
    ‖globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
          data analysis chart sameAction physical shift firstParameter hFirst -
        globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
          data analysis chart sameAction physical shift secondParameter hSecond‖ ≤
      |firstParameter - secondParameter| *
        (shift.coerciveShift.coercivityConstant - |firstParameter|)⁻¹ *
        (shift.coerciveShift.coercivityConstant - |secondParameter|)⁻¹ :=
  finiteDefectReducedRealResolvent_sub_opNorm_le
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    (globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    shift.coerciveShift firstParameter secondParameter hFirst hSecond

/-- Public Candidate-A resolvent-identity gate. -/
theorem global_candidateA_augmented_reduced_resolvent_identity_gate
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
    (firstParameter secondParameter : Real)
    (hFirst : |firstParameter| < shift.coerciveShift.coercivityConstant)
    (hSecond : |secondParameter| < shift.coerciveShift.coercivityConstant) :
    globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
        data analysis chart sameAction physical shift firstParameter hFirst -
      globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
        data analysis chart sameAction physical shift secondParameter hSecond =
      (firstParameter - secondParameter) •
        ((globalCandidateAAugmentedReducedRealResolvent period hPeriod
            configuration data analysis chart sameAction physical shift
            firstParameter hFirst).comp
          (globalCandidateAAugmentedReducedRealResolvent period hPeriod
            configuration data analysis chart sameAction physical shift
            secondParameter hSecond)) ∧
      ‖globalCandidateAAugmentedReducedRealResolvent period hPeriod configuration
            data analysis chart sameAction physical shift firstParameter hFirst -
          globalCandidateAAugmentedReducedRealResolvent period hPeriod
            configuration data analysis chart sameAction physical shift
            secondParameter hSecond‖ ≤
        |firstParameter - secondParameter| *
          (shift.coerciveShift.coercivityConstant - |firstParameter|)⁻¹ *
          (shift.coerciveShift.coercivityConstant - |secondParameter|)⁻¹ :=
  ⟨globalCandidateAAugmentedReducedRealResolvent_identity period hPeriod
      configuration data analysis chart sameAction physical shift firstParameter
        secondParameter hFirst hSecond,
    globalCandidateAAugmentedReducedRealResolvent_sub_opNorm_le period hPeriod
      configuration data analysis chart sameAction physical shift firstParameter
        secondParameter hFirst hSecond⟩

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedReducedResolventIdentity4D
end JanusFormal
