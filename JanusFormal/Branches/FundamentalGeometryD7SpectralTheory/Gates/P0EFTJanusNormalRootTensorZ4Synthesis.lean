import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusNormalOrientationZ4Lift
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusSymmetricTensorOneFiveCandidate

namespace JanusFormal
namespace P0EFTJanusNormalRootTensorZ4Synthesis

set_option autoImplicit false

open P0EFTJanusNormalOrientationZ4Lift
open P0EFTJanusSymmetricTensorOneFiveCandidate
open P0EFTJanusPeriodicQuarterCompetition

/--
Candidate internal sector derived from two independent pieces of geometry:

* the one-sided throat normal line supplies an order-four square-root phase;
* the three-dimensional symmetric tensor bundle supplies the trace/traceless
  rank decomposition `1+5`.
-/
structure NormalRootTensorCandidate where
  normalRootPhase : NormalRootPhase
  normalRootLaw : IsNormalSquareRoot normalRootPhase

/-- The normal-root phase is necessarily one of the PT-conjugate quarter phases. -/
theorem candidate_phase_is_one_or_three
    (s : NormalRootTensorCandidate) :
    s.normalRootPhase = 1 \/ s.normalRootPhase = 3 :=
  (normal_square_root_iff_one_or_three s.normalRootPhase).mp
    s.normalRootLaw

/-- PT conjugation defines the other candidate. -/
def ptConjugateCandidate
    (s : NormalRootTensorCandidate) : NormalRootTensorCandidate :=
  { normalRootPhase := ptConjugatePhase s.normalRootPhase
    normalRootLaw :=
      pt_preserves_normal_square_roots
        s.normalRootPhase s.normalRootLaw }

/-- PT changes the selected root. -/
theorem pt_conjugate_candidate_has_distinct_phase
    (s : NormalRootTensorCandidate) :
    (ptConjugateCandidate s).normalRootPhase ≠
      s.normalRootPhase :=
  normal_square_root_is_not_pt_fixed
    s.normalRootPhase s.normalRootLaw

/-- The tensor-bundle determinant weights are independent of which conjugate root is chosen. -/
theorem candidate_tensor_weights_are_one_to_five
    (_s : NormalRootTensorCandidate) :
    periodicTraceDeterminantWeight = 1 /\
      quarterTracelessDeterminantWeight = 5 :=
  trace_traceless_determinant_weights_are_one_to_five

/-- Both conjugate roots give the same arithmetic `1:5` stationarity polynomial. -/
theorem candidate_one_five_stationarity
    (_s : NormalRootTensorCandidate) :
    stationarityPolynomial
      periodicTraceDeterminantWeight
      quarterTracelessDeterminantWeight
      (1 / 3) = 0 :=
  trace_traceless_one_five_stationary_root

/-- The normal square-root character squares to the canonical normal half-turn. -/
theorem candidate_character_squares_to_normal_line
    (s : NormalRootTensorCandidate)
    (winding : ℤ) :
    normalRootCharacter s.normalRootPhase winding +
        normalRootCharacter s.normalRootPhase winding =
      normalHalfTurnCharacter winding :=
  square_root_character_squares_to_normal_holonomy
    s.normalRootPhase s.normalRootLaw winding

/--
Combined theorem matrix: topology fixes the conjugate quarter-phase pair, while
three-dimensional tensor geometry fixes the off-shell `1:5` rank split.
-/
theorem normal_root_tensor_candidate_matrix
    (s : NormalRootTensorCandidate) :
    (s.normalRootPhase = 1 \/ s.normalRootPhase = 3) /\
    ((ptConjugateCandidate s).normalRootPhase ≠
      s.normalRootPhase) /\
    periodicTraceDeterminantWeight = 1 /\
    quarterTracelessDeterminantWeight = 5 /\
    stationarityPolynomial
      periodicTraceDeterminantWeight
      quarterTracelessDeterminantWeight
      (1 / 3) = 0 := by
  exact ⟨candidate_phase_is_one_or_three s,
    pt_conjugate_candidate_has_distinct_phase s,
    trace_traceless_determinant_weights_are_one_to_five.1,
    trace_traceless_determinant_weights_are_one_to_five.2,
    candidate_one_five_stationarity s⟩

/--
This is the strongest geometric origin currently available for the internal
quarter sector: it does not derive a new irreducible rank-five representation
from the cyclic fundamental group.  Instead, the order-four phase is a square
root of the one-sided normal holonomy and the integer five is the rank of
traceless symmetric two-tensors on the three-dimensional throat.

Physical closure still requires the actual normal-root line bundle, the doubled
real tensor fields, gauge fixing, ghosts, masses and the full superdeterminant.
-/
structure NormalRootTensorPhysicalStatus where
  oneSidedNormalLineConstructed : Prop
  normalComplexSquareRootConstructed : Prop
  ptConjugateRootPairDerived : Prop
  doubledSymmetricTensorBundleConstructed : Prop
  globalTraceTracelessSplittingProved : Prop
  normalRootCoupledOnlyToTracelessSector : Prop
  traceSectorPeriodicDerived : Prop
  fullQuadraticOperatorDerived : Prop
  gaugeGhostSuperdeterminantComputed : Prop
  oneFiveEffectiveRatioSurvives : Prop
  stableOneThirdRootSurvives : Prop
  finiteCountertermsFixedMicroscopically : Prop
  noObservedScaleImported : Prop


def normalRootTensorPhysicalClosure
    (s : NormalRootTensorPhysicalStatus) : Prop :=
  s.oneSidedNormalLineConstructed /\
  s.normalComplexSquareRootConstructed /\
  s.ptConjugateRootPairDerived /\
  s.doubledSymmetricTensorBundleConstructed /\
  s.globalTraceTracelessSplittingProved /\
  s.normalRootCoupledOnlyToTracelessSector /\
  s.traceSectorPeriodicDerived /\
  s.fullQuadraticOperatorDerived /\
  s.gaugeGhostSuperdeterminantComputed /\
  s.oneFiveEffectiveRatioSurvives /\
  s.stableOneThirdRootSurvives /\
  s.finiteCountertermsFixedMicroscopically /\
  s.noObservedScaleImported

end P0EFTJanusNormalRootTensorZ4Synthesis
end JanusFormal
