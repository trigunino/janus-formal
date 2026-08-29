import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCanonicalShapeTrace4D

/-!
# H10 mobile-boundary action-source bridge

This gate records that the mobile two-sheet non-null boundary used by H10 is
not a second boundary functional. Once the unique global Candidate-A action
data selects the canonical two-sheet source, its GHY summand is exactly the
already constructed mobile two-sheet GHY action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped BigOperators
open MeasureTheory
open P0EFTJanusFiniteStratifiedBoundaryVariation
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The canonical mobile two-sheet datum is evaluated by the unique
Candidate-A GHY summand, with no duplicated scalar boundary action. -/
theorem globalCandidateAGHYAction_eq_mobile_twoSheet_ledger
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (faces : Fin 2 → CanonicalLatitudeBase → NonNullFaceDatum)
    (hSource : data.nonNullBoundary =
      (.canonicalLatitudeTwoSheet faces :
        GlobalCandidateANonNullBoundaryDatum period hPeriod NonNullFace)) :
    globalCandidateAGHYAction period hPeriod data =
      ∑ sheet : Fin 2, ∫ base, nonNullGHYCurve (faces sheet base) 0
        ∂canonicalLatitudeBaseMeasure period := by
  unfold globalCandidateAGHYAction
  rw [hSource]
  exact globalCandidateANonNullBoundaryAction_canonicalLatitudeTwoSheet
    period hPeriod faces

/-- Strong H10 action-source bridge: selecting the concrete normal-graph datum
inside the sole Candidate-A non-null boundary slot gives exactly the genuine
mobile two-sheet GHY action already constructed from the induced metric,
canonical unit normal, Gauss--Weingarten curvature and induced measure. -/
theorem globalCandidateAGHYAction_normalGraph_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (hSource : data.nonNullBoundary =
      normalGraphCanonicalCandidateANonNullBoundaryDatum period hPeriod
        (NonNullFace := NonNullFace) einsteinScale metric displacement parameter
          hNonNull) :
    globalCandidateAGHYAction period hPeriod data =
      normalGraphCanonicalTwoSheetGaussGHYAction period hPeriod einsteinScale
        metric displacement parameter hNonNull := by
  unfold globalCandidateAGHYAction
  rw [hSource]
  exact globalCandidateANonNullBoundaryAction_normalGraph_eq period hPeriod
    einsteinScale metric displacement parameter hNonNull

set_option backward.isDefEq.respectTransparency false in
/-- Smooth-core H10 source identification.  Once the residual redundant-frame
trace theorem is supplied, the completed `C²` two-sheet action is literally
the GHY summand of the unique central Candidate-A action datum. -/
theorem candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA
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
    (hTrace : CandidateANormalBoundaryHistoricalGaussTraceAgreement period
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
  rw [candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_gauss
    period hPeriod einsteinScale metric hTransverse tensor variedMetric hVaried
      displacement parameter hNonNull hCurrent hNormalRootNonneg
        hVolumeRootNonneg hTrace]
  exact (globalCandidateAGHYAction_normalGraph_eq period hPeriod data
    einsteinScale variedMetric displacement parameter hNonNull hSource).symm

set_option backward.isDefEq.respectTransparency false in
/-- Terminal H10 source bridge with the canonical shape installed.  The only
remaining geometric input is the exact redundant-frame encoding of
`(g₀⁻¹h) ∘ (h⁻¹K)`; the trace identity and the passage to the unique central
Candidate-A action are then automatic. -/
theorem candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_of_encodingAgreement
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
    (hEncoding : CandidateANormalBoundaryHistoricalGaussEncodingAgreement
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
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA
      period hPeriod data einsteinScale metric hTransverse tensor variedMetric
        hVaried displacement parameter hNonNull hCurrent hNormalRootNonneg
          hVolumeRootNonneg
          (candidateANormalBoundaryHistoricalGaussTraceAgreement_of_encodingAgreement
            period hPeriod metric tensor variedMetric hVaried displacement
              parameter hNonNull hCurrent.1.1.2 hEncoding)
          hSource

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D
end JanusFormal
