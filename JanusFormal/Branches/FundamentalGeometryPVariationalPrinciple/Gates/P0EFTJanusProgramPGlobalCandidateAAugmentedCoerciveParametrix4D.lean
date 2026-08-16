import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveShift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectCoerciveShiftInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D

/-!
# Canonical Candidate-A parametrix from coercivity and shifted surjectivity

The augmented Candidate-A generalized inverse is no longer an independent
packet.  It is the inverse of `H + P`, where `P` is the finite defect projector.
The identities proved by the generic coercive-shift layer identify both H12
defects with `P` itself.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveParametrix4D

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectCoerciveShiftInverse4D

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

private abbrev AugmentedHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) augmentedHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup (AugmentedHilbert period hPeriod configuration data
      analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) augmentedHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real (AugmentedHilbert period hPeriod configuration data
      analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) augmentedHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace (AugmentedHilbert period hPeriod configuration data
      analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The canonical bounded Candidate-A parametrix. -/
noncomputable def globalCandidateAAugmentedCoerciveParametrix
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
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift)) :
    AugmentedHilbert period hPeriod configuration data analysis →L[Real]
      AugmentedHilbert period hPeriod configuration data analysis :=
  finiteDefectCanonicalParametrix
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical) shift hSurjective

/-- The canonical left H12 defect equals the finite projector. -/
theorem globalCandidateAAugmentedKernelDefect_eq_projection
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
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift)) :
    globalCandidateAAugmentedKernelDefect period hPeriod configuration data
        analysis chart sameAction physical
          (globalCandidateAAugmentedCoerciveParametrix period hPeriod
            configuration data analysis chart sameAction physical shift
              hSurjective) =
      shift.projection := by
  unfold globalCandidateAAugmentedKernelDefect
  rw [finiteDefectCanonicalParametrix_comp_operator
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical) shift hSurjective]
  abel

/-- The canonical right H12 defect equals the same finite projector. -/
theorem globalCandidateAAugmentedCokernelDefect_eq_projection
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
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift)) :
    globalCandidateAAugmentedCokernelDefect period hPeriod configuration data
        analysis chart sameAction physical
          (globalCandidateAAugmentedCoerciveParametrix period hPeriod
            configuration data analysis chart sameAction physical shift
              hSurjective) =
      shift.projection := by
  unfold globalCandidateAAugmentedCokernelDefect
  rw [operator_comp_finiteDefectCanonicalParametrix
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical) shift hSurjective]
  abel

/-- Construct the pre-existing generalized-inverse H12 packet from the
coercive shift and its surjectivity. -/
noncomputable def globalCandidateAFaithfulAugmentedGeneralizedInverse_of_coerciveShift
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
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift))
    (hLLStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :
    GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period hPeriod
      configuration data analysis chart sameAction physical where
  parametrix := globalCandidateAAugmentedCoerciveParametrix period hPeriod
    configuration data analysis chart sameAction physical shift hSurjective
  generalized_inverse :=
    operator_parametrix_operator
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) shift hSurjective
  kernelDefect_range_finite := by
    rw [globalCandidateAAugmentedKernelDefect_eq_projection period hPeriod
      configuration data analysis chart sameAction physical shift hSurjective]
    exact shift.projection_range_finite
  cokernelDefect_range_finite := by
    rw [globalCandidateAAugmentedCokernelDefect_eq_projection period hPeriod
      configuration data analysis chart sameAction physical shift hSurjective]
    exact shift.projection_range_finite
  ll_stationary := hLLStationary

/-- Full H12 gate through the existing generalized-inverse adapter. -/
theorem global_candidateA_h12_fredholm_gate_of_coerciveShift
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
    (hSurjective : Function.Surjective
      (finiteDefectShiftedOperator
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical) shift))
    (hLLStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :=
  global_candidateA_h12_faithful_augmented_fredholm_gate_of_generalizedInverse
    period hPeriod configuration data analysis chart sameAction physical
      (globalCandidateAFaithfulAugmentedGeneralizedInverse_of_coerciveShift
        period hPeriod configuration data analysis chart sameAction physical
          shift hSurjective hLLStationary)

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveParametrix4D
end JanusFormal
