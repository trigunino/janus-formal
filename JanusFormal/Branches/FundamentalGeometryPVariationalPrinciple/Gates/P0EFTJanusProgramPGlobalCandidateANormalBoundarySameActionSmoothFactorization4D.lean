import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionGermHessian4D

/-!
# Smooth-source factorization of the H10 same-action germ

The terminal H10 certificate identifies every smooth presentation of one
completed admissible parameter with the same completed two-sheet GHY value.
This file records the resulting representation independence explicitly: two
smooth metric-normal presentations of the same completed parameter produce
exactly the same central Candidate-A GHY summand.

Thus the mobile Candidate-A source factors through the completed functional
core on the physical germ.  No representative is selected and no additional
action, metric, normal, chart, geometric datum or axiom is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance smoothFactorizationCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance smoothFactorizationCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance smoothFactorizationCandidateANormalBoundaryFunctionalCoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreCompleteSpace period hPeriod metric

/-- Two smooth presentations of the same completed admissible parameter give
the same value of the unique central Candidate-A non-null boundary summand. -/
theorem
    candidateANormalBoundaryGlobalCandidateAGHYAction_smooth_representation_independent
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hSame : CandidateANormalBoundarySameActionAtSmoothCurrent period hPeriod
      data einsteinScale metric current)
    (firstTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (firstMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hFirstVaried :
      firstMetric.tensor = metric.metric.tensor + firstTensor)
    (firstDisplacement : SmoothNormalDisplacement period hPeriod)
    (firstParameter : Real)
    (hFirstCurrent : current =
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (firstTensor, firstDisplacement), firstParameter))
    (secondTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (secondMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hSecondVaried :
      secondMetric.tensor = metric.metric.tensor + secondTensor)
    (secondDisplacement : SmoothNormalDisplacement period hPeriod)
    (secondParameter : Real)
    (hSecondCurrent : current =
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (secondTensor, secondDisplacement), secondParameter)) :
    let hFirstNonNull :=
      normalGraphNonNullAt_of_candidate_GHY_mem period hPeriod metric
        firstTensor firstMetric hFirstVaried firstDisplacement firstParameter
          (hFirstCurrent ▸ hSame.1)
    let hSecondNonNull :=
      normalGraphNonNullAt_of_candidate_GHY_mem period hPeriod metric
        secondTensor secondMetric hSecondVaried secondDisplacement
          secondParameter (hSecondCurrent ▸ hSame.1)
    globalCandidateAGHYAction period hPeriod
        (normalGraphCanonicalCandidateAActionData period hPeriod data
          einsteinScale firstMetric firstDisplacement firstParameter
            hFirstNonNull) =
      globalCandidateAGHYAction period hPeriod
        (normalGraphCanonicalCandidateAActionData period hPeriod data
          einsteinScale secondMetric secondDisplacement secondParameter
            hSecondNonNull) := by
  have hFirst :=
    hSame.2 firstTensor firstMetric hFirstVaried firstDisplacement
      firstParameter hFirstCurrent hSame.1
  have hSecond :=
    hSame.2 secondTensor secondMetric hSecondVaried secondDisplacement
      secondParameter hSecondCurrent hSame.1
  simpa only using hFirst.symm.trans hSecond

/-- Pointwise certificate that the smooth mobile source has a unique value on
one completed admissible parameter.  The factorization field depends on the
same stored domain proof, so no representative or proof witness is chosen a
second time. -/
structure CandidateANormalBoundarySmoothSourceFactorizationAtCurrent
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    Prop where
  domain : current ∈
    candidateANormalBoundaryGHYDomain period hPeriod metric
  factorizes :
    ∀ (firstTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
      (firstMetric : SmoothGeneralLorentzMetric period hPeriod)
      (hFirstVaried :
        firstMetric.tensor = metric.metric.tensor + firstTensor)
      (firstDisplacement : SmoothNormalDisplacement period hPeriod)
      (firstParameter : Real)
      (hFirstCurrent : current =
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (firstTensor, firstDisplacement), firstParameter))
      (secondTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
      (secondMetric : SmoothGeneralLorentzMetric period hPeriod)
      (hSecondVaried :
        secondMetric.tensor = metric.metric.tensor + secondTensor)
      (secondDisplacement : SmoothNormalDisplacement period hPeriod)
      (secondParameter : Real)
      (hSecondCurrent : current =
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (secondTensor, secondDisplacement), secondParameter)),
      let hFirstNonNull :=
        normalGraphNonNullAt_of_candidate_GHY_mem period hPeriod metric
          firstTensor firstMetric hFirstVaried firstDisplacement firstParameter
            (hFirstCurrent ▸ domain)
      let hSecondNonNull :=
        normalGraphNonNullAt_of_candidate_GHY_mem period hPeriod metric
          secondTensor secondMetric hSecondVaried secondDisplacement
            secondParameter (hSecondCurrent ▸ domain)
      globalCandidateAGHYAction period hPeriod
          (normalGraphCanonicalCandidateAActionData period hPeriod data
            einsteinScale firstMetric firstDisplacement firstParameter
              hFirstNonNull) =
        globalCandidateAGHYAction period hPeriod
          (normalGraphCanonicalCandidateAActionData period hPeriod data
            einsteinScale secondMetric secondDisplacement secondParameter
              hSecondNonNull)

/-- The pointwise same-action theorem supplies the smooth-source factorization
certificate without any additional hypothesis. -/
theorem
    candidateANormalBoundarySmoothSourceFactorizationAtCurrent_of_sameAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hSame : CandidateANormalBoundarySameActionAtSmoothCurrent period hPeriod
      data einsteinScale metric current) :
    CandidateANormalBoundarySmoothSourceFactorizationAtCurrent period hPeriod
      data einsteinScale metric current := by
  refine { domain := hSame.1, factorizes := ?_ }
  intro firstTensor firstMetric hFirstVaried firstDisplacement firstParameter
    hFirstCurrent secondTensor secondMetric hSecondVaried secondDisplacement
      secondParameter hSecondCurrent
  exact
    candidateANormalBoundaryGlobalCandidateAGHYAction_smooth_representation_independent
      period hPeriod data einsteinScale metric current hSame firstTensor
        firstMetric hFirstVaried firstDisplacement firstParameter hFirstCurrent
        secondTensor secondMetric hSecondVaried secondDisplacement
          secondParameter hSecondCurrent

/-- Representation independence holds on the same genuine neighborhood of
zero as the terminal H10 same-action certificate. -/
theorem
    candidateANormalBoundarySmoothSourceFactorization_eventually
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ∀ᶠ current in 𝓝
        (0 : Prod
          (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real),
      CandidateANormalBoundarySmoothSourceFactorizationAtCurrent period hPeriod
        data einsteinScale metric current := by
  filter_upwards
    [candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eventually_eq_globalCandidateA_smooth
      period hPeriod data einsteinScale metric hTransverse] with current hSame
  exact
    candidateANormalBoundarySmoothSourceFactorizationAtCurrent_of_sameAction
      period hPeriod data einsteinScale metric current hSame

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D
end JanusFormal
