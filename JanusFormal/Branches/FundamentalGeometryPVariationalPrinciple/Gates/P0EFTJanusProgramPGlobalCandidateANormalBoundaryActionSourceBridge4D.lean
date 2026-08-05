import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

/-!
# H10 mobile-boundary action-source bridge

This gate records that the mobile two-sheet non-null boundary used by H10 is
not a second boundary functional.  Once the unique global Candidate-A action
data selects the canonical two-sheet source, its GHY summand is definitionally
the already existing two-sheet ledger integral.
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

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D
end JanusFormal
