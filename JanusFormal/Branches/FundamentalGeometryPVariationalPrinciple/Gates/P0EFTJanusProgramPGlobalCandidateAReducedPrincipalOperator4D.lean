import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAReducedCanonicalEnergies4D

/-!
# Riesz operator of the canonical reduced principal Candidate-A Hessian

The canonical principal form on `(ker H_actual)ᗮ` is bounded and symmetric.
Its Riesz representative is therefore a bounded self-adjoint operator on that
same actual complement.  This operator is used only to state the five diagonal
and one off-diagonal principal estimates at operator level; it does not replace
the actual augmented Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAReducedPrincipalOperator4D

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 2500000

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
open P0EFTJanusProgramPGlobalCandidateAReducedCanonicalEnergies4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
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

private abbrev ActualComplement
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
  SelfAdjointKernelComplement
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)

/-- Riesz representative of the genuine reduced principal form. -/
def globalCandidateAReducedPrincipalOperator
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
    ActualComplement period hPeriod configuration data analysis chart sameAction
        physical →L[Real]
      ActualComplement period hPeriod configuration data analysis chart
        sameAction physical :=
  @InnerProductSpace.continuousLinearMapOfBilin
    Real
    (ActualComplement period hPeriod configuration data analysis chart sameAction
      physical)
    inferInstance inferInstance inferInstance inferInstance
    (globalCandidateAReducedPrincipalForm period hPeriod configuration data
      analysis chart sameAction physical)

/-- Exact Riesz pairing with the canonical reduced principal form. -/
theorem globalCandidateAReducedPrincipalOperator_pairing
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
    (first second : ActualComplement period hPeriod configuration data analysis
      chart sameAction physical) :
    inner Real
        (globalCandidateAReducedPrincipalOperator period hPeriod configuration
          data analysis chart sameAction physical first)
        second =
      globalCandidateAReducedPrincipalForm period hPeriod configuration data
        analysis chart sameAction physical first second := by
  exact @InnerProductSpace.continuousLinearMapOfBilin_apply
    Real
    (ActualComplement period hPeriod configuration data analysis chart sameAction
      physical)
    inferInstance inferInstance inferInstance inferInstance
    (globalCandidateAReducedPrincipalForm period hPeriod configuration data
      analysis chart sameAction physical) first second

/-- Self-adjointness follows from symmetry of the genuine principal form. -/
theorem globalCandidateAReducedPrincipalOperator_isSelfAdjoint
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
    IsSelfAdjoint
      (globalCandidateAReducedPrincipalOperator period hPeriod configuration data
        analysis chart sameAction physical) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  calc
    inner Real
        (globalCandidateAReducedPrincipalOperator period hPeriod configuration
          data analysis chart sameAction physical first) second =
      globalCandidateAReducedPrincipalForm period hPeriod configuration data
        analysis chart sameAction physical first second :=
      globalCandidateAReducedPrincipalOperator_pairing period hPeriod
        configuration data analysis chart sameAction physical first second
    _ = globalCandidateAReducedPrincipalForm period hPeriod configuration data
        analysis chart sameAction physical second first :=
      globalCandidateAReducedPrincipalForm_symmetric period hPeriod
        configuration data analysis chart sameAction physical first second
    _ = inner Real
        (globalCandidateAReducedPrincipalOperator period hPeriod configuration
          data analysis chart sameAction physical second) first :=
      (globalCandidateAReducedPrincipalOperator_pairing period hPeriod
        configuration data analysis chart sameAction physical second first).symm
    _ = inner Real first
        (globalCandidateAReducedPrincipalOperator period hPeriod configuration
          data analysis chart sameAction physical second) :=
      real_inner_comm _ _

/-- Public reduced-principal operator checkpoint. -/
theorem global_candidateA_reduced_principal_operator_gate
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
    IsSelfAdjoint
      (globalCandidateAReducedPrincipalOperator period hPeriod configuration data
        analysis chart sameAction physical) ∧
    (∀ first second,
      inner Real
          (globalCandidateAReducedPrincipalOperator period hPeriod configuration
            data analysis chart sameAction physical first) second =
        globalCandidateAReducedPrincipalForm period hPeriod configuration data
          analysis chart sameAction physical first second) :=
  ⟨globalCandidateAReducedPrincipalOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical,
    globalCandidateAReducedPrincipalOperator_pairing period hPeriod
      configuration data analysis chart sameAction physical⟩

end
end P0EFTJanusProgramPGlobalCandidateAReducedPrincipalOperator4D
end JanusFormal
