import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D

/-!
# H12 from an orthogonal finite defect and one global lower bound

The augmented Candidate-A Riesz representative is already self-adjoint.  The
preceding lower-bound packet nevertheless stored self-adjointness of the full
shift `H + P` as a separate field.  For the finite-dimensional spectral defect
used in the Fredholm construction this is redundant: it is enough to prove that
`P` is an orthogonal, hence self-adjoint, projection.

This file combines the existing self-adjointness theorem for the augmented
operator with self-adjointness of `P`, derives self-adjointness of `H + P`, and
reuses the direct estimate

`‖x‖ ≤ C ‖(H + P) x‖`

to construct surjectivity, the shifted inverse, the generalized inverse, the
finite defects and the H12 Fredholm/index-zero certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalLowerBoundShift4D

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option synthInstance.maxHeartbeats 1900000

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveShift4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
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
  lowerBoundNormedAddCommGroup
  lowerBoundInnerProductSpace
  lowerBoundCompleteSpace

def orthogonalLowerRieszOperator
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
    LowerBoundHilbert period hPeriod configuration data analysis →L[Real]
      LowerBoundHilbert period hPeriod configuration data analysis :=
  globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
    data analysis chart sameAction physical

def orthogonalLowerProjection
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
  @FiniteDefectCoerciveShiftData.projection
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical)
    shift

/-- The remaining H12 packet after using self-adjointness of the augmented
Hessian itself.  Only orthogonality of the finite defect and the direct global
lower bound remain as new operator input. -/
structure GlobalCandidateAAugmentedOrthogonalLowerBoundShift4D
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
  projection_selfAdjoint : IsSelfAdjoint
    (orthogonalLowerProjection period hPeriod configuration data analysis chart
      sameAction physical coerciveShift)
  lowerBoundConstant : NNReal
  shifted_lowerBound : ∀ vector :
      LowerBoundHilbert period hPeriod configuration data analysis,
    ‖vector‖ ≤ (lowerBoundConstant : Real) *
      ‖augmentedLowerBoundShiftedApply period hPeriod configuration data
        analysis chart sameAction physical coerciveShift vector‖
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- The faithful augmented operator is the same self-adjoint Riesz
representative already constructed by H11. -/
theorem orthogonalLowerRieszOperator_isSelfAdjoint
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
      (orthogonalLowerRieszOperator period hPeriod configuration data analysis
        chart sameAction physical) := by
  exact
    P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D.globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint
      period hPeriod configuration data analysis chart sameAction physical

/-- Orthogonality of the finite defect makes the whole shifted operator
self-adjoint. -/
theorem globalCandidateAAugmentedOrthogonalShift_isSelfAdjoint
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
    (shift : GlobalCandidateAAugmentedOrthogonalLowerBoundShift4D period hPeriod
      configuration data analysis chart sameAction physical) :
    IsSelfAdjoint
      (augmentedLowerBoundShiftedOperator period hPeriod configuration data
        analysis chart sameAction physical shift.coerciveShift) := by
  change IsSelfAdjoint
    (orthogonalLowerRieszOperator period hPeriod configuration data analysis
      chart sameAction physical +
    orthogonalLowerProjection period hPeriod configuration data analysis chart
      sameAction physical shift.coerciveShift)
  exact
    (orthogonalLowerRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical).add
        shift.projection_selfAdjoint

/-- Convert the orthogonal-defect packet into the preceding lower-bound packet. -/
def GlobalCandidateAAugmentedOrthogonalLowerBoundShift4D.toLowerBound
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
    (shift : GlobalCandidateAAugmentedOrthogonalLowerBoundShift4D period hPeriod
      configuration data analysis chart sameAction physical) :
    GlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D period hPeriod
      configuration data analysis chart sameAction physical where
  coerciveShift := shift.coerciveShift
  shifted_selfAdjoint :=
    globalCandidateAAugmentedOrthogonalShift_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical shift
  lowerBoundConstant := shift.lowerBoundConstant
  shifted_lowerBound := shift.shifted_lowerBound
  ll_stationary := shift.ll_stationary

/-- The direct global estimate and orthogonality of the defect produce the full
H12 Fredholm certificate. -/
def global_candidateA_h12_fredholm_gate_of_orthogonalLowerBoundShift
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
    (shift : GlobalCandidateAAugmentedOrthogonalLowerBoundShift4D period hPeriod
      configuration data analysis chart sameAction physical) :=
  global_candidateA_h12_fredholm_gate_of_selfAdjointLowerBoundShift period
    hPeriod configuration data analysis chart sameAction physical
      (shift.toLowerBound period hPeriod)

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalLowerBoundShift4D
end JanusFormal
