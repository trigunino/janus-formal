import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectGlobalLowerBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalLowerBoundShift4D

/-!
# H12 from an orthogonal finite defect and off-defect coercivity

The preceding generic estimate shows that the global shifted lower bound is
already implied by the original finite-defect coercivity data.  Therefore the
Candidate-A H12 packet can be reduced once more.

The only operator-specific input is now:

* a finite idempotent defect projector annihilated by the augmented Hessian on
  both sides;
* coercivity of the augmented Hessian on `ker P`;
* self-adjointness of `P`;
* the stationary LL stratum.

The norm estimate for `H + P`, shifted self-adjointness, dense range,
surjectivity, bounded inverse, generalized inverse, finite defects, Fredholm
property and index zero are all constructed downstream.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedCoerciveShift4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalLowerBoundShift4D
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectGlobalLowerBound4D
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

section RawTransports

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
  NonNullFace NullFace measure)
variable (sameAction :
  ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D period hPeriod
    configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
  hPeriod configuration data analysis chart sameAction)
variable (shift : GlobalCandidateAAugmentedCoerciveShiftData4D period hPeriod
  configuration data analysis chart sameAction physical)

theorem orthogonalLowerProjection_idempotent : ∀ vector :
    LowerBoundHilbert period hPeriod configuration data analysis,
    orthogonalLowerProjection period hPeriod configuration data analysis chart
        sameAction physical shift
      (orthogonalLowerProjection period hPeriod configuration data analysis
        chart sameAction physical shift vector) =
      orthogonalLowerProjection period hPeriod configuration data analysis chart
        sameAction physical shift vector := by
  let canonicalOperator :=
    globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical
  let canonicalProjection :=
    @FiniteDefectCoerciveShiftData.projection
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      canonicalOperator shift
  intro vector
  change canonicalProjection (canonicalProjection vector) =
    canonicalProjection vector
  exact @FiniteDefectCoerciveShiftData.projection_idempotent
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    canonicalOperator shift vector

theorem orthogonalLowerProjection_annihilates_riesz : ∀ vector :
    LowerBoundHilbert period hPeriod configuration data analysis,
    orthogonalLowerProjection period hPeriod configuration data analysis chart
      sameAction physical shift
        (orthogonalLowerRieszOperator period hPeriod configuration data analysis
          chart sameAction physical vector) = 0 := by
  let canonicalOperator :=
    globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical
  let canonicalProjection :=
    @FiniteDefectCoerciveShiftData.projection
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis)
      (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
        analysis)
      (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
      canonicalOperator shift
  intro vector
  change canonicalProjection (canonicalOperator vector) = 0
  exact @FiniteDefectCoerciveShiftData.projection_annihilates_operator
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    canonicalOperator shift vector

theorem orthogonalLowerRiesz_annihilates_projection
    (vector : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
        data analysis chart sameAction physical
      ((@FiniteDefectCoerciveShiftData.projection
          (GlobalCandidateAFaithfulSameActionHilbert period hPeriod
            configuration data analysis)
          (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
            analysis)
          (augmentedFredholmNormedSpace period hPeriod configuration data
            analysis)
          (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
            configuration data analysis chart sameAction physical)
          shift) vector) = 0 :=
  @FiniteDefectCoerciveShiftData.operator_annihilates_projection
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift vector

def orthogonalLowerCoercivityConstant : Real :=
  @FiniteDefectCoerciveShiftData.coercivityConstant
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift

theorem orthogonalLowerCoercivityConstant_pos :
    0 < orthogonalLowerCoercivityConstant period hPeriod configuration data
      analysis chart sameAction physical shift := by
  exact @FiniteDefectCoerciveShiftData.coercivityConstant_pos
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift

def orthogonalLower_coercive_off_defect :=
  @FiniteDefectCoerciveShiftData.coercive_off_defect
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift

def orthogonalLowerShiftControlData :=
  @FiniteDefectCoerciveShiftData.toShiftControlData
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    shift

def orthogonalLowerRawBound : NNReal :=
  @finiteDefectShiftControlBound
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    (orthogonalLowerShiftControlData period hPeriod configuration data analysis
      chart sameAction physical shift)

theorem augmentedLowerBoundShiftedApply_eq_alias
    (vector : LowerBoundHilbert period hPeriod configuration data analysis) :
    augmentedLowerBoundShiftedApply period hPeriod configuration data analysis
        chart sameAction physical shift vector =
      @finiteDefectShiftControlOperator
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis)
        (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical)
        (orthogonalLowerShiftControlData period hPeriod configuration data
          analysis chart sameAction physical shift)
        vector := by
  rfl

theorem lowerBoundNorm_eq_canonical
    (vector : LowerBoundHilbert period hPeriod configuration data analysis) :
    ‖vector‖ =
      @norm
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis)
        (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
          analysis).toNorm
        vector := by
  rfl

theorem orthogonalLower_shifted_lowerBound : ∀ vector :
    LowerBoundHilbert period hPeriod configuration data analysis,
    ‖vector‖ ≤
      (orthogonalLowerRawBound period hPeriod configuration data analysis chart
        sameAction physical shift : Real) *
      ‖augmentedLowerBoundShiftedApply period hPeriod configuration data
        analysis chart sameAction physical shift vector‖ := by
  intro vector
  have hRaw := @finiteDefectShiftControl_globalLowerBound
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    (orthogonalLowerShiftControlData period hPeriod configuration data analysis
      chart sameAction physical shift)
    vector
  calc
    ‖vector‖ =
        @norm
          (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
            data analysis)
          (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
            analysis).toNorm
          vector :=
      lowerBoundNorm_eq_canonical period hPeriod configuration data analysis
        vector
    _ ≤
        (orthogonalLowerRawBound period hPeriod configuration data analysis chart
          sameAction physical shift : Real) *
          @norm
            (GlobalCandidateAFaithfulSameActionHilbert period hPeriod
              configuration data analysis)
            (augmentedFredholmNormedAddCommGroup period hPeriod configuration data
              analysis).toNorm
            (@finiteDefectShiftControlOperator
              (GlobalCandidateAFaithfulSameActionHilbert period hPeriod
                configuration data analysis)
              (augmentedFredholmNormedAddCommGroup period hPeriod configuration
                data analysis)
              (augmentedFredholmNormedSpace period hPeriod configuration data
                analysis)
              (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
                configuration data analysis chart sameAction physical)
              (orthogonalLowerShiftControlData period hPeriod configuration data
                analysis chart sameAction physical shift)
              vector) := by
        simpa only [orthogonalLowerRawBound] using hRaw
    _ = (orthogonalLowerRawBound period hPeriod configuration data analysis chart
          sameAction physical shift : Real) *
        ‖augmentedLowerBoundShiftedApply period hPeriod configuration data
          analysis chart sameAction physical shift vector‖ := by
      rw [lowerBoundNorm_eq_canonical period hPeriod configuration data analysis]
      rw [← augmentedLowerBoundShiftedApply_eq_alias period hPeriod
        configuration data analysis chart sameAction physical shift vector]

end RawTransports

/-- Narrowest current Candidate-A H12 packet.  The shifted lower bound and
shifted self-adjointness are both conclusions. -/
structure GlobalCandidateAAugmentedOrthogonalCoerciveShift4D
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
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Reconstruct the orthogonal lower-bound packet using the explicit Banach
estimate proved from the coercivity data. -/
def GlobalCandidateAAugmentedOrthogonalCoerciveShift4D.toLowerBound
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis chart sameAction physical) :
    GlobalCandidateAAugmentedOrthogonalLowerBoundShift4D period hPeriod
      configuration data analysis chart sameAction physical where
  coerciveShift := shift.coerciveShift
  projection_selfAdjoint := shift.projection_selfAdjoint
  lowerBoundConstant :=
    orthogonalLowerRawBound period hPeriod configuration data analysis chart
      sameAction physical shift.coerciveShift
  shifted_lowerBound :=
    orthogonalLower_shifted_lowerBound period hPeriod configuration data analysis
      chart sameAction physical shift.coerciveShift
  ll_stationary := shift.ll_stationary

/-- The off-defect coercivity and orthogonality packet produces the complete
H12 Fredholm certificate. -/
def global_candidateA_h12_fredholm_gate_of_orthogonalCoerciveShift
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
      configuration data analysis chart sameAction physical) :=
  global_candidateA_h12_fredholm_gate_of_orthogonalLowerBoundShift period
    hPeriod configuration data analysis chart sameAction physical
      (shift.toLowerBound period hPeriod)

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D
end JanusFormal
