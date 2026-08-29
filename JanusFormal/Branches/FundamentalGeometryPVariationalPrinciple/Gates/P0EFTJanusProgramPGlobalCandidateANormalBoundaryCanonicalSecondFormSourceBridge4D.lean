import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCanonicalEncodingReduction4D

/-!
# Terminal H10 source bridge from the scalar second-form identity

All inverse-matrix, redundant-frame and trace algebra has already been removed
upstream.  This facade records that the sole remaining scalar geometric
identity -- equality of the historical and pulled-back canonical second
fundamental forms on the installed generators -- is sufficient to identify
the completed two-sheet `C²` functional with the unique central Candidate-A
GHY summand.
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
/-- H10 source identification after reducing the remaining geometry to the
scalar equality of the historical and canonical second fundamental forms. -/
theorem candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_of_pulledBackSecondForm
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
    (hSecondForm :
      CandidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull)
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
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_of_encodingAgreement
      period hPeriod data einsteinScale metric hTransverse tensor variedMetric
        hVaried displacement parameter hNonNull hCurrent hNormalRootNonneg
          hVolumeRootNonneg
          (candidateANormalBoundaryHistoricalGaussEncodingAgreement_of_pulledBackSecondForm
            period hPeriod metric tensor variedMetric displacement parameter
              hNonNull hSecondForm)
          hSource

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D
end JanusFormal
