import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveParametrix4D

/-!
# H12 from a self-adjoint finite-defect shift with a norm lower bound

For elliptic estimates, the natural datum is the unbundled estimate

`‖x‖ ≤ C ‖(H + P) x‖`.

This file derives shifted surjectivity directly from that estimate and then
constructs the generalized inverse, finite defects, Fredholmness and index
zero.  No explicit range or inverse witness remains in the input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D

set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 1700000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveShift4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveParametrix4D
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D
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

attribute [local instance 30000]
  augmentedFredholmNormedAddCommGroup
  augmentedFredholmInnerProductSpace
  augmentedFredholmCompleteSpace

/-- Local opaque name for the canonical faithful augmented Hilbert space. -/
def LowerBoundHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) : Type :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

abbrev lowerBoundNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (LowerBoundHilbert period hPeriod configuration data analysis) :=
  augmentedFredholmNormedAddCommGroup period hPeriod configuration data analysis

attribute [local instance 30000] lowerBoundNormedAddCommGroup

local instance (priority := 30000) lowerBoundInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (LowerBoundHilbert period hPeriod configuration data analysis) :=
  augmentedFredholmInnerProductSpace period hPeriod configuration data analysis

local instance (priority := 30000) lowerBoundCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (LowerBoundHilbert period hPeriod configuration data analysis) :=
  augmentedFredholmCompleteSpace period hPeriod configuration data analysis

/-- The finite-defect shifted augmented Hessian on the canonical faithful
Hilbert space. -/
def augmentedLowerBoundShiftedOperator
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
    LowerBoundHilbert period hPeriod configuration data analysis →L[Real]
      LowerBoundHilbert period hPeriod configuration data analysis :=
  @finiteDefectShiftedOperator
    (LowerBoundHilbert period hPeriod configuration data analysis)
    (lowerBoundNormedAddCommGroup period hPeriod configuration data analysis)
    inferInstance
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical)
    shift

/-- Pointwise shifted augmented Hessian, avoiding any comparison of bundled
continuous-linear-map instance parameters. -/
def augmentedLowerBoundShiftedApply
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
      configuration data analysis chart sameAction physical)
    (vector : LowerBoundHilbert period hPeriod configuration data analysis) :
    LowerBoundHilbert period hPeriod configuration data analysis :=
  globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical vector +
    (@FiniteDefectCoerciveShiftData.projection
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical)
      shift) vector

theorem augmentedLowerBoundShiftedOperator_apply
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
      configuration data analysis chart sameAction physical)
    (vector : LowerBoundHilbert period hPeriod configuration data analysis) :
    augmentedLowerBoundShiftedOperator period hPeriod configuration data
        analysis chart sameAction physical shift vector =
      augmentedLowerBoundShiftedApply period hPeriod configuration data analysis
        chart sameAction physical shift vector := by
  rfl

/-- PDE-facing H12 packet: one finite-defect coercive shift, self-adjointness,
and one global norm estimate. -/
structure GlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D
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
      hPeriod configuration data analysis chart sameAction) : Type where
  coerciveShift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
    configuration data analysis chart sameAction physical
  shifted_selfAdjoint : IsSelfAdjoint
    (augmentedLowerBoundShiftedOperator period hPeriod configuration data
      analysis chart sameAction physical coerciveShift)
  lowerBoundConstant : NNReal
  shifted_lowerBound : ∀ vector :
      LowerBoundHilbert period hPeriod configuration data analysis,
    ‖vector‖ ≤ (lowerBoundConstant : Real) *
      ‖augmentedLowerBoundShiftedApply period hPeriod configuration data
        analysis chart sameAction physical coerciveShift vector‖
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Surjectivity of the shifted augmented Hessian from the explicit norm
estimate. -/
theorem globalCandidateAAugmentedShiftedOperator_surjective_of_lowerBound
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
    (shift : GlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D period
      hPeriod configuration data analysis chart sameAction physical) :
    Function.Surjective
      (augmentedLowerBoundShiftedOperator period hPeriod configuration data
        analysis chart sameAction physical shift.coerciveShift) := by
  rcases shift with ⟨coerciveShift, hSelf, constant, hBound, _⟩
  have hOperatorBound : ∀ vector :
      LowerBoundHilbert period hPeriod configuration data analysis,
      ‖vector‖ ≤ (constant : Real) *
        ‖augmentedLowerBoundShiftedOperator period hPeriod configuration data
          analysis chart sameAction physical coerciveShift vector‖ := by
    intro vector
    rw [augmentedLowerBoundShiftedOperator_apply]
    exact hBound vector
  exact @selfAdjoint_surjective_of_globalLowerBound
    (LowerBoundHilbert period hPeriod configuration data analysis)
    (lowerBoundNormedAddCommGroup period hPeriod configuration data analysis)
    (lowerBoundInnerProductSpace period hPeriod configuration data analysis)
    (lowerBoundCompleteSpace period hPeriod configuration data analysis)
    (augmentedLowerBoundShiftedOperator period hPeriod configuration data
      analysis chart sameAction physical coerciveShift)
    hSelf constant hOperatorBound

/-- Construct the generalized inverse directly from the PDE-facing lower-bound
packet. -/
noncomputable def
    globalCandidateAFaithfulAugmentedGeneralizedInverse_of_selfAdjointLowerBoundShift
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
    (shift : GlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D period
      hPeriod configuration data analysis chart sameAction physical) :
    GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period hPeriod
      configuration data analysis chart sameAction physical :=
  globalCandidateAFaithfulAugmentedGeneralizedInverse_of_coerciveShift
    period hPeriod configuration data analysis chart sameAction physical
      shift.coerciveShift
      (globalCandidateAAugmentedShiftedOperator_surjective_of_lowerBound period
        hPeriod configuration data analysis chart sameAction physical shift)
      shift.ll_stationary

/-- Full H12 Fredholm/index-zero gate from the shifted global norm estimate. -/
def global_candidateA_h12_fredholm_gate_of_selfAdjointLowerBoundShift
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
    (shift : GlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D period
      hPeriod configuration data analysis chart sameAction physical) :=
  global_candidateA_h12_faithful_augmented_fredholm_gate_of_generalizedInverse
    period hPeriod configuration data analysis chart sameAction physical
      (globalCandidateAFaithfulAugmentedGeneralizedInverse_of_selfAdjointLowerBoundShift
        period hPeriod configuration data analysis chart sameAction physical
          shift)

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D
end JanusFormal
