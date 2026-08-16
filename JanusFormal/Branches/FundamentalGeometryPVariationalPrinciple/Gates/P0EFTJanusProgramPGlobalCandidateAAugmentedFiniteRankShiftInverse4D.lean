import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D

/-!
# H12 generalized inverse from an invertible finite-rank shift

For a self-adjoint Fredholm operator the most concrete parametrix is obtained by
adding the finite-dimensional kernel/cokernel projection.  If `P` is an
idempotent finite-rank projection annihilated by the augmented Hessian `H` on
both sides and `H + P` has a bounded inverse `Q`, then

`QP = PQ = P`, `QH = HQ = I - P`, and therefore `HQH = H`.

This file proves those identities at the level of the actual Candidate-A
augmented Riesz operator.  The canonical left and right defects of the existing
H12 generalized-inverse package are both exactly `P`; their finite-dimensional
ranges are therefore inherited from a single finite-rank projection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedFiniteRankShiftInverse4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
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

private abbrev ShiftHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) shiftHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup (ShiftHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) shiftHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (ShiftHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) shiftHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real (ShiftHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) shiftHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real (ShiftHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) shiftHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace (ShiftHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

private abbrev ShiftEndomorphism
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  ShiftHilbert period hPeriod configuration data analysis →L[Real]
    ShiftHilbert period hPeriod configuration data analysis

/-- A finite-rank spectral correction making the augmented Hessian boundedly
invertible.  In applications `defectProjection` is the orthogonal projection
onto the finite-dimensional zero-mode space. -/
structure GlobalCandidateAFaithfulAugmentedFiniteRankShiftInverse4D
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
  defectProjection : ShiftEndomorphism period hPeriod configuration data analysis
  projection_idempotent :
    defectProjection.comp defectProjection = defectProjection
  operator_comp_projection :
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical).comp defectProjection = 0
  projection_comp_operator :
    defectProjection.comp
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical) = 0
  shiftedInverse : ShiftEndomorphism period hPeriod configuration data analysis
  inverse_comp_shift :
    shiftedInverse.comp
      (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical +
        defectProjection) =
      ContinuousLinearMap.id Real
        (ShiftHilbert period hPeriod configuration data analysis)
  shift_comp_inverse :
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
          data analysis chart sameAction physical + defectProjection).comp
        shiftedInverse =
      ContinuousLinearMap.id Real
        (ShiftHilbert period hPeriod configuration data analysis)
  defect_range_finite : FiniteDimensional Real defectProjection.range
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- The inverse of `H + P` fixes the finite defect range. -/
theorem finiteRankShift_inverse_comp_projection
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
    (shift : GlobalCandidateAFaithfulAugmentedFiniteRankShiftInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :
    shift.shiftedInverse.comp shift.defectProjection =
      shift.defectProjection := by
  let operator := globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
    configuration data analysis chart sameAction physical
  ext vector
  have hInverse := congrArg
    (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
      map (shift.defectProjection vector)) shift.inverse_comp_shift
  have hOperatorProjection := congrArg
    (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
      map vector) shift.operator_comp_projection
  have hProjectionProjection := congrArg
    (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
      map vector) shift.projection_idempotent
  change shift.shiftedInverse
      (operator (shift.defectProjection vector) +
        shift.defectProjection (shift.defectProjection vector)) =
    shift.defectProjection vector at hInverse
  change operator (shift.defectProjection vector) = 0 at hOperatorProjection
  change shift.defectProjection (shift.defectProjection vector) =
    shift.defectProjection vector at hProjectionProjection
  rw [hOperatorProjection, hProjectionProjection, zero_add] at hInverse
  exact hInverse

/-- The defect projection also fixes the image of the shifted inverse. -/
theorem finiteRankShift_projection_comp_inverse
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
    (shift : GlobalCandidateAFaithfulAugmentedFiniteRankShiftInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :
    shift.defectProjection.comp shift.shiftedInverse =
      shift.defectProjection := by
  let operator := globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
    configuration data analysis chart sameAction physical
  have hProjectionShift :
      shift.defectProjection.comp (operator + shift.defectProjection) =
        shift.defectProjection := by
    ext vector
    have hProjectionOperator := congrArg
      (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
        map vector) shift.projection_comp_operator
    have hProjectionProjection := congrArg
      (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
        map vector) shift.projection_idempotent
    change shift.defectProjection (operator vector) = 0 at hProjectionOperator
    change shift.defectProjection (shift.defectProjection vector) =
      shift.defectProjection vector at hProjectionProjection
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
    rw [map_add, hProjectionOperator, hProjectionProjection, zero_add]
  ext vector
  have hProjectionShiftAt := congrArg
    (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
      map (shift.shiftedInverse vector)) hProjectionShift
  have hRight := congrArg
    (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
      map vector) shift.shift_comp_inverse
  change
    shift.defectProjection
        ((operator + shift.defectProjection) (shift.shiftedInverse vector)) =
      shift.defectProjection (shift.shiftedInverse vector)
    at hProjectionShiftAt
  change (operator + shift.defectProjection) (shift.shiftedInverse vector) =
    vector at hRight
  rw [hRight] at hProjectionShiftAt
  exact hProjectionShiftAt.symm

/-- The left canonical defect `I - QH` is exactly the finite-rank projection. -/
theorem finiteRankShift_kernelDefect_eq_projection
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
    (shift : GlobalCandidateAFaithfulAugmentedFiniteRankShiftInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :
    globalCandidateAAugmentedKernelDefect period hPeriod configuration data
        analysis chart sameAction physical shift.shiftedInverse =
      shift.defectProjection := by
  let operator := globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
    configuration data analysis chart sameAction physical
  ext vector
  have hLeft := congrArg
    (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
      map vector) shift.inverse_comp_shift
  have hQP := congrArg
    (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
      map vector)
    (finiteRankShift_inverse_comp_projection period hPeriod configuration data
      analysis chart sameAction physical shift)
  change shift.shiftedInverse (operator vector + shift.defectProjection vector) =
    vector at hLeft
  change shift.shiftedInverse (shift.defectProjection vector) =
    shift.defectProjection vector at hQP
  rw [map_add, hQP] at hLeft
  unfold globalCandidateAAugmentedKernelDefect
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply]
  calc
    vector - shift.shiftedInverse (operator vector) =
        (shift.shiftedInverse (operator vector) +
          shift.defectProjection vector) -
            shift.shiftedInverse (operator vector) := by rw [hLeft]
    _ = shift.defectProjection vector := by abel

/-- The right canonical defect `I - HQ` is the same projection. -/
theorem finiteRankShift_cokernelDefect_eq_projection
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
    (shift : GlobalCandidateAFaithfulAugmentedFiniteRankShiftInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :
    globalCandidateAAugmentedCokernelDefect period hPeriod configuration data
        analysis chart sameAction physical shift.shiftedInverse =
      shift.defectProjection := by
  let operator := globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
    configuration data analysis chart sameAction physical
  ext vector
  have hRight := congrArg
    (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
      map vector) shift.shift_comp_inverse
  have hPQ := congrArg
    (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
      map vector)
    (finiteRankShift_projection_comp_inverse period hPeriod configuration data
      analysis chart sameAction physical shift)
  change operator (shift.shiftedInverse vector) +
    shift.defectProjection (shift.shiftedInverse vector) = vector at hRight
  change shift.defectProjection (shift.shiftedInverse vector) =
    shift.defectProjection vector at hPQ
  rw [hPQ] at hRight
  unfold globalCandidateAAugmentedCokernelDefect
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply]
  calc
    vector - operator (shift.shiftedInverse vector) =
        (operator (shift.shiftedInverse vector) +
          shift.defectProjection vector) -
            operator (shift.shiftedInverse vector) := by rw [hRight]
    _ = shift.defectProjection vector := by abel

/-- The inverse of the finite-rank shift is the canonical generalized inverse
of the original augmented Hessian. -/
def globalCandidateAFaithfulAugmentedGeneralizedInverse_of_finiteRankShift
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
    (shift : GlobalCandidateAFaithfulAugmentedFiniteRankShiftInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :
    GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period hPeriod
      configuration data analysis chart sameAction physical where
  parametrix := shift.shiftedInverse
  generalized_inverse := by
    let operator := globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical
    ext vector
    have hRight := congrArg
      (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
        map (operator vector)) shift.shift_comp_inverse
    have hPQ := congrArg
      (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
        map (operator vector))
      (finiteRankShift_projection_comp_inverse period hPeriod configuration data
        analysis chart sameAction physical shift)
    have hPH := congrArg
      (fun map : ShiftEndomorphism period hPeriod configuration data analysis =>
        map vector) shift.projection_comp_operator
    change operator (shift.shiftedInverse (operator vector)) +
      shift.defectProjection (shift.shiftedInverse (operator vector)) =
        operator vector at hRight
    change shift.defectProjection (shift.shiftedInverse (operator vector)) =
      shift.defectProjection (operator vector) at hPQ
    change shift.defectProjection (operator vector) = 0 at hPH
    rw [hPQ, hPH, add_zero] at hRight
    exact hRight
  kernelDefect_range_finite := by
    rw [finiteRankShift_kernelDefect_eq_projection period hPeriod configuration
      data analysis chart sameAction physical shift]
    exact shift.defect_range_finite
  cokernelDefect_range_finite := by
    rw [finiteRankShift_cokernelDefect_eq_projection period hPeriod configuration
      data analysis chart sameAction physical shift]
    exact shift.defect_range_finite
  ll_stationary := shift.ll_stationary

/-- H12 from one finite-rank spectral shift and the bounded inverse of the
shifted augmented Hessian. -/
theorem global_candidateA_h12_faithful_augmented_fredholm_gate_of_finiteRankShift
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
    (shift : GlobalCandidateAFaithfulAugmentedFiniteRankShiftInverse4D period
      hPeriod configuration data analysis chart sameAction physical) :=
  global_candidateA_h12_faithful_augmented_fredholm_gate_of_generalizedInverse
    period hPeriod configuration data analysis chart sameAction physical
      (globalCandidateAFaithfulAugmentedGeneralizedInverse_of_finiteRankShift
        period hPeriod configuration data analysis chart sameAction physical
          shift)

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedFiniteRankShiftInverse4D
end JanusFormal
