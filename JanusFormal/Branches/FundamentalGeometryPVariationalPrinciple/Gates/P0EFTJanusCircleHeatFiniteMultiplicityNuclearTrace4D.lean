import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceClass

/-!
# Finite internal multiplicity of the circle nuclear heat expansion

Finite degeneracy preserves the concrete nuclear certificate: multiply every
rank-one Fourier component by the same natural multiplicity.  The operator
sum and nuclear trace acquire exactly that factor.  This is a finite-sector
bridge only; it does not construct the global Janus operator.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatFiniteMultiplicityNuclearTrace4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleHeatSemigroupOperator
open P0EFTJanusCircleHeatNuclearTraceClass

/-- Rank-one heat component with a finite internal degeneracy. -/
def circleHeatFiniteMultiplicityRankOne
    (multiplicity : Nat) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) (mode : Int) :
    CircleHilbert →L[Complex] CircleHilbert :=
  (multiplicity : Complex) • circleHeatRankOne time fold twist mode

theorem circleHeatFiniteMultiplicityRankOne_summable
    (multiplicity : Nat) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) :
    Summable (circleHeatFiniteMultiplicityRankOne multiplicity time fold twist) := by
  exact ((circleHeatRankOne_summable time fold twist).hasSum.const_smul
    (multiplicity : Complex)).summable

/-- The nuclear operator sum is exactly the finite multiple of the circle
heat semigroup. -/
theorem circleHeatFiniteMultiplicity_tsum_eq
    (multiplicity : Nat) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) :
    (∑' mode : Int,
        circleHeatFiniteMultiplicityRankOne multiplicity time fold twist mode) =
      (multiplicity : Complex) •
        circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist := by
  rw [show (∑' mode : Int,
      circleHeatFiniteMultiplicityRankOne multiplicity time fold twist mode) =
      (multiplicity : Complex) • circleHeatNuclearSum time fold twist by
    exact ((circleHeatRankOne_summable time fold twist).hasSum.const_smul
      (multiplicity : Complex)).tsum_eq]
  rw [circleHeatNuclearSum_eq_semigroup]

/-- Finite multiplicity preserves summability of component operator norms. -/
theorem circleHeatFiniteMultiplicityRankOne_norm_summable
    (multiplicity : Nat) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) :
    Summable (fun mode : Int =>
      ‖circleHeatFiniteMultiplicityRankOne multiplicity time fold twist mode‖) :=
  by
    have h := (circleHeatRankOne_norm_summable time fold twist).hasSum.const_smul
      (multiplicity : Real)
    exact h.summable.congr fun mode => by
      simp [circleHeatFiniteMultiplicityRankOne, norm_smul]

/-- Nuclear trace with finite internal multiplicity. -/
def circleHeatFiniteMultiplicityNuclearTrace
    (multiplicity : Nat) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) : Real :=
  multiplicity * circleHeatNuclearTrace time fold twist

theorem circleHeatFiniteMultiplicityNuclearTrace_pt_eq_positive
    (multiplicity : Nat) (time : HeatTime) (twist : CircleTwist) :
    circleHeatFiniteMultiplicityNuclearTrace multiplicity time .pt twist =
      circleHeatFiniteMultiplicityNuclearTrace multiplicity time .positive twist := by
  rw [circleHeatFiniteMultiplicityNuclearTrace,
    circleHeatFiniteMultiplicityNuclearTrace,
    circleHeatNuclearTrace_pt_eq_positive]

end

end P0EFTJanusCircleHeatFiniteMultiplicityNuclearTrace4D
end JanusFormal
