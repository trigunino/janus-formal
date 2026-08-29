import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCanonicalSecondFormSourceBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCompletedGaussCanonicalSecondFormReduction4D

/-!
# Terminal H10 action source from the completed Gauss identification

This facade removes the historical second-form hypothesis from the terminal
action theorem.  The sole remaining input is now the direct equality between
the completed Candidate-A Gauss form and the canonical pulled-back shape
pairing on the installed generators.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

set_option backward.isDefEq.respectTransparency false in
/-- H10 source identification reduced to the direct completed-Gauss/canonical
second-form equality. -/
theorem candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_of_completedGaussCanonical
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric)
    (hNormalRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hVolumeRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hCanonical :
      CandidateANormalBoundaryCompletedGaussCanonicalSecondFormAgreement period
        hPeriod metric tensor variedMetric displacement parameter hNonNull)
    (hSource : data.nonNullBoundary =
      normalGraphCanonicalCandidateANonNullBoundaryDatum period hPeriod
        (NonNullFace := NonNullFace) einsteinScale variedMetric displacement
          parameter hNonNull) :
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) =
      globalCandidateAGHYAction period hPeriod data := by
  exact
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_of_pulledBackSecondForm
      period hPeriod data einsteinScale metric hTransverse tensor variedMetric
        hVaried displacement parameter hNonNull hCurrent hNormalRootNonneg
          hVolumeRootNonneg
          (candidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement_of_completedGaussCanonical
            period hPeriod metric hTransverse tensor variedMetric hVaried
              displacement parameter hNonNull hCurrent.1
                hNormalRootNonneg hCanonical)
          hSource

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D
end JanusFormal
