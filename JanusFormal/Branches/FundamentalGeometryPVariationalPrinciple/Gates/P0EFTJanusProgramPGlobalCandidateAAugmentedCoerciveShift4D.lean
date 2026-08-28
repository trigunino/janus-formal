import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectCoerciveShift4D

/-!
# Coercive finite-defect shift for the augmented Candidate-A Hessian

This file applies the generic finite-defect coercivity gate to the actual
augmented same-action Riesz operator.  It removes two redundant H12 inputs:
finite-dimensionality of the kernel and injectivity of the shifted operator.
Both follow from one coercive estimate on the complement of the finite defect.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveShift4D

set_option autoImplicit false
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
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D

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

/-- Candidate-A specialization of the generic coercive finite-defect packet. -/
def GlobalCandidateAAugmentedCoerciveShiftData4D
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
  @FiniteDefectCoerciveShiftData
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmNormedAddCommGroup
      period hPeriod configuration data analysis)
    (P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.augmentedFredholmNormedSpace
      period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical)

/-- Coercivity off the defect forces the actual augmented Candidate-A kernel to
be finite-dimensional. -/
theorem globalCandidateAAugmentedRieszOperator_kernel_finite_of_coerciveShift
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
    (shift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
      configuration data analysis chart sameAction physical) :
    FiniteDimensional Real
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).ker := by
  letI := augmentedFredholmNormedAddCommGroup period hPeriod configuration data
    analysis
  letI := augmentedFredholmNormedSpace period hPeriod configuration data analysis
  letI := augmentedFredholmModule period hPeriod configuration data analysis
  letI hFinite :=
    @FiniteDefectCoerciveShiftData.projection_range_finite
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) shift
  exact @Submodule.finiteDimensional_of_le
    Real
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    inferInstance inferInstance
    (augmentedFredholmModule period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical).ker
    _ hFinite
    (@operator_ker_le_projection_range
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) shift)

/-- The shifted augmented Candidate-A operator is automatically injective. -/
theorem globalCandidateAAugmentedShiftedOperator_injective_of_coerciveShift
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
    (shift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
      configuration data analysis chart sameAction physical) :
    Function.Injective
      (@finiteDefectShiftedOperator
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift) :=
  @finiteDefectShiftedOperator_injective
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical) shift

/-- Therefore H12 only needs a range/surjectivity argument for the coercively
shifted operator; its injectivity and finite kernel are already fixed. -/
theorem globalCandidateA_augmented_coercive_shift_gate
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
    (shift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
      configuration data analysis chart sameAction physical) :
    FiniteDimensional Real
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).ker ∧
    Function.Injective
      (@finiteDefectShiftedOperator
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift) :=
  ⟨globalCandidateAAugmentedRieszOperator_kernel_finite_of_coerciveShift
      period hPeriod configuration data analysis chart sameAction physical shift,
    globalCandidateAAugmentedShiftedOperator_injective_of_coerciveShift
      period hPeriod configuration data analysis chart sameAction physical shift⟩

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveShift4D
end JanusFormal
