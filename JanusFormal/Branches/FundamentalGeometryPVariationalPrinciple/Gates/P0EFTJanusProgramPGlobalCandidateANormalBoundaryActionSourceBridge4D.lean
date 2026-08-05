import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCompletedGaussWeingartenClosure4D

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

noncomputable section

open scoped BigOperators
open MeasureTheory
open P0EFTJanusFiniteStratifiedBoundaryVariation
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

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

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D
end JanusFormal
