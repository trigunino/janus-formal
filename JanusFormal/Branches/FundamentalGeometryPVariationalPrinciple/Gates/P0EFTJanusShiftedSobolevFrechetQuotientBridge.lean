import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFrechetPullbackQuotientHessian
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevQuotientSameActionHessian

/-!
# Bridge to the generic Frechet quotient-Hessian descent

The periodic coefficient action already has a genuine second Frechet
derivative and a continuous Hessian on the normed zero-mode quotient.  This
gate proves that the latter is exactly the unique algebraic quotient descent
constructed by the generic Frechet infrastructure.  It remains a statement
about the periodic coefficient model, not the nonlinear global Janus action.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedSobolevFrechetQuotientBridge

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusLatticeFourierSaintVenantExactness
open P0EFTJanusWeightedL2LatticeSaintVenantExactness
open P0EFTJanusShiftedSobolevLatticeLorentzGram
open P0EFTJanusShiftedSobolevPullbackHessian
open P0EFTJanusShiftedSobolevSameActionHessian
open P0EFTJanusShiftedSobolevPhysicalQuotient
open P0EFTJanusShiftedSobolevQuotientSameActionHessian
open P0EFTJanusFrechetPullbackQuotientHessian

def shiftedCoefficientActionHessianLinear
    (targetWeight : LatticeMode → Real) :
    ShiftedPotentialHilbert targetWeight →ₗ[Real]
      ShiftedPotentialHilbert targetWeight →ₗ[Real] Real :=
  continuousHessianToLinear
    (shiftedCoefficientActionHessian targetWeight)

theorem shiftedCoefficientActionHessianLinear_annihilates_zeroMode_left
    (targetWeight : LatticeMode → Real)
    (gauge : ShiftedPotentialHilbert targetWeight)
    (hGauge : gauge ∈ (potentialZeroModeProjection targetWeight).range)
    (direction : ShiftedPotentialHilbert targetWeight) :
    shiftedCoefficientActionHessianLinear targetWeight gauge direction = 0 := by
  have hKernel :
      gauge ∈ (shiftedSobolevLorentzGram targetWeight).ker := by
    rw [← zeroModeProjection_range_eq_symbol_ker targetWeight]
    exact hGauge
  change shiftedSobolevLorentzGram targetWeight gauge = 0 at hKernel
  change ⟪shiftedPullbackHessian targetWeight gauge, direction⟫_Real = 0
  rw [shiftedPullbackHessian_pairing, hKernel]
  simp

theorem shiftedCoefficientActionHessianLinear_annihilates_zeroMode_right
    (targetWeight : LatticeMode → Real)
    (gauge : ShiftedPotentialHilbert targetWeight)
    (hGauge : gauge ∈ (potentialZeroModeProjection targetWeight).range)
    (direction : ShiftedPotentialHilbert targetWeight) :
    shiftedCoefficientActionHessianLinear targetWeight direction gauge = 0 := by
  have hKernel :
      gauge ∈ (shiftedSobolevLorentzGram targetWeight).ker := by
    rw [← zeroModeProjection_range_eq_symbol_ker targetWeight]
    exact hGauge
  change shiftedSobolevLorentzGram targetWeight gauge = 0 at hKernel
  change ⟪shiftedPullbackHessian targetWeight direction, gauge⟫_Real = 0
  rw [shiftedPullbackHessian_pairing, hKernel]
  simp

/-- The generic algebraic quotient descent of the same coefficient-action
Hessian. -/
def genericShiftedCoefficientQuotientHessian
    (targetWeight : LatticeMode → Real) :
    PhysicalPotentialQuotient targetWeight →ₗ[Real]
      PhysicalPotentialQuotient targetWeight →ₗ[Real] Real :=
  quotientHessian
    (shiftedCoefficientActionHessianLinear targetWeight)
    (potentialZeroModeProjection targetWeight).range
    (shiftedCoefficientActionHessianLinear_annihilates_zeroMode_left
      targetWeight)
    (shiftedCoefficientActionHessianLinear_annihilates_zeroMode_right
      targetWeight)

/-- The continuous Hessian obtained by differentiating the quotient action is
exactly the generic unique quotient descent. -/
theorem physicalQuotientActionHessian_eq_generic_descent
    (targetWeight : LatticeMode → Real) :
    continuousHessianToLinear
        (physicalQuotientActionHessian targetWeight) =
      genericShiftedCoefficientQuotientHessian targetWeight := by
  apply quotientHessian_unique
    (shiftedCoefficientActionHessianLinear targetWeight)
    (potentialZeroModeProjection targetWeight).range
    (shiftedCoefficientActionHessianLinear_annihilates_zeroMode_left
      targetWeight)
    (shiftedCoefficientActionHessianLinear_annihilates_zeroMode_right
      targetWeight)
  intro first second
  change
    physicalQuotientActionHessian targetWeight
        (Submodule.Quotient.mk first) (Submodule.Quotient.mk second) =
      shiftedCoefficientActionHessian targetWeight first second
  rw [physicalQuotientActionHessian_mk_mk]
  rfl

theorem shifted_sobolev_frechet_quotient_bridge_gate
    (targetWeight : LatticeMode → Real) :
    continuousHessianToLinear
        (physicalQuotientActionHessian targetWeight) =
      quotientHessian
        (shiftedCoefficientActionHessianLinear targetWeight)
        (potentialZeroModeProjection targetWeight).range
        (shiftedCoefficientActionHessianLinear_annihilates_zeroMode_left
          targetWeight)
        (shiftedCoefficientActionHessianLinear_annihilates_zeroMode_right
          targetWeight) :=
  physicalQuotientActionHessian_eq_generic_descent targetWeight

end

end P0EFTJanusShiftedSobolevFrechetQuotientBridge
end JanusFormal
