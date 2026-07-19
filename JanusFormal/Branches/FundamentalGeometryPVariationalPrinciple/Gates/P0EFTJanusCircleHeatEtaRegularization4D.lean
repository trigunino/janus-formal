import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceDerivative
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleBoundedTransformSpectralFlow

/-!
# Sectorial circle heat eta

This gate constructs the positive-time circle series
`sum_n lambda_n exp (-t lambda_n^2)`.  It proves absolute summability, PT
oddness, and the endpoint large-gauge Fourier relabeling.  It does not assert
an APS eta invariant, a zero-time limit, or geometric anomaly inflow.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatEtaRegularization4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatNuclearTraceContinuity
open P0EFTJanusCircleHeatNuclearTraceDerivative
open P0EFTJanusCircleBoundedTransformSpectralFlow

/-- The modewise positive-time heat eta coefficient. -/
def circleHeatEtaSummand
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : Int) : Real :=
  diracEigenvalue fold twist mode * heatWeight time fold twist mode

/-- Absolute convergence of the sectorial circle heat eta series. -/
theorem circleHeatEtaSummand_summable
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (circleHeatEtaSummand time fold twist) := by
  apply Summable.of_norm_bounded
    ((heatWeight_summable time fold twist).sub
      (circleHeatWeightRealDerivative_summable time fold twist))
  intro mode
  let eigenvalue := diracEigenvalue fold twist mode
  have hEigenvalue : |eigenvalue| <= 1 + eigenvalue ^ 2 := by
    have hSquare := sq_nonneg (|eigenvalue| - 1 / 2)
    ring_nf at hSquare
    rw [sq_abs] at hSquare
    nlinarith
  have hWeight : 0 <= heatWeight time fold twist mode := by
    exact (Real.exp_pos _).le
  calc
    ‖circleHeatEtaSummand time fold twist mode‖ =
        |eigenvalue| * heatWeight time fold twist mode := by
          simp [circleHeatEtaSummand, eigenvalue, Real.norm_eq_abs,
            abs_of_nonneg hWeight]
    _ <= (1 + eigenvalue ^ 2) * heatWeight time fold twist mode :=
      mul_le_mul_of_nonneg_right hEigenvalue hWeight
    _ = heatWeight time fold twist mode -
        circleHeatWeightRealDerivative time.1 fold twist mode := by
      simp [circleHeatWeightRealDerivative, circleHeatWeightReal,
        heatWeight, circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
        eigenvalueSq, eigenvalue]
      ring

/-- The convergent sectorial circle heat eta at positive time. -/
def circleHeatEta
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) : Real :=
  tsum (circleHeatEtaSummand time fold twist)

/-- PT reverses the heat eta sign at fixed twist and positive time. -/
theorem circleHeatEta_pt_eq_neg_positive
    (time : HeatTime) (twist : CircleTwist) :
    circleHeatEta time .pt twist = -circleHeatEta time .positive twist := by
  unfold circleHeatEta
  calc
    tsum (circleHeatEtaSummand time .pt twist) =
        tsum (fun mode => -circleHeatEtaSummand time .positive twist mode) := by
      apply tsum_congr
      intro mode
      simp [circleHeatEtaSummand, heatWeight, eigenvalueSq, diracEigenvalue]
    _ = -tsum (circleHeatEtaSummand time .positive twist) := tsum_neg

/-- Unit holonomy is the periodic heat eta after the exact relabeling
`mode |-> mode + 1`. -/
theorem circleHeatEta_unit_eq_periodic
    (time : HeatTime) (fold : Fold) :
    circleHeatEta time fold unitCircleTwist =
      circleHeatEta time fold periodicTwist := by
  unfold circleHeatEta
  calc
    tsum (circleHeatEtaSummand time fold unitCircleTwist) =
        tsum (fun mode : Int =>
          circleHeatEtaSummand time fold periodicTwist (mode + 1)) := by
      apply tsum_congr
      intro mode
      simp [circleHeatEtaSummand, heatWeight, eigenvalueSq,
        diracEigenvalue_unit_relabel]
    _ = tsum (circleHeatEtaSummand time fold periodicTwist) := by
      simpa using
        (Equiv.addRight (1 : Int)).tsum_eq
          (circleHeatEtaSummand time fold periodicTwist)

end

end P0EFTJanusCircleHeatEtaRegularization4D
end JanusFormal
