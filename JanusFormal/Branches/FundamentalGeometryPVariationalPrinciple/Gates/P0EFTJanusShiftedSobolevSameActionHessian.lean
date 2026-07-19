import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevPullbackHessian

/-!
# The shifted Sobolev pullback as the Hessian of one action

This gate stays entirely inside the periodic `Z^4` coefficient model.  It
defines the quadratic action `1/2 * ||J u||^2` on the already completed source
space and proves that its genuine second Frechet derivative is the previously
constructed operator `J^adjoint J`.  It does not identify this coefficient
action with the nonlinear global Janus action.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedSobolevSameActionHessian

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusLatticeFourierSaintVenantExactness
open P0EFTJanusWeightedL2LatticeSaintVenantExactness
open P0EFTJanusShiftedSobolevLatticeLorentzGram
open P0EFTJanusShiftedSobolevPullbackHessian

/-- The target identity action whose Hessian is the target identity pairing. -/
def shiftedTargetIdentityAction
    (targetWeight : LatticeMode → Real)
    (tensor : SobolevMetricHilbert targetWeight) : Real :=
  (1 / 2 : Real) * ⟪tensor, tensor⟫_Real

/-- The honest quadratic action associated with the shifted Lorentz--Gram
operator in the periodic coefficient model. -/
def shiftedCoefficientAction
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) : Real :=
  (1 / 2 : Real) *
    ⟪shiftedSobolevLorentzGram targetWeight potential,
      shiftedSobolevLorentzGram targetWeight potential⟫_Real

theorem shiftedCoefficientAction_eq_target_comp
    (targetWeight : LatticeMode → Real) :
    shiftedCoefficientAction targetWeight =
      shiftedTargetIdentityAction targetWeight ∘
        shiftedSobolevLorentzGram targetWeight := rfl

theorem shiftedCoefficientAction_add_kernel
    (targetWeight : LatticeMode → Real)
    (potential gauge : ShiftedPotentialHilbert targetWeight)
    (hGauge : shiftedSobolevLorentzGram targetWeight gauge = 0) :
    shiftedCoefficientAction targetWeight (potential + gauge) =
      shiftedCoefficientAction targetWeight potential := by
  simp [shiftedCoefficientAction, map_add, hGauge]

/-- The real Riesz map on the completed coefficient space, written without a
finite-dimensionality assumption. -/
def shiftedCoefficientRiesz
    (targetWeight : LatticeMode → Real) :
    ShiftedPotentialHilbert targetWeight →L[Real]
      ShiftedPotentialHilbert targetWeight →L[Real] Real :=
  LinearMap.mkContinuous₂ (innerₗ (ShiftedPotentialHilbert targetWeight)) 1
    (fun first second => by
      change ‖inner Real first second‖ ≤
        1 * ‖first‖ * ‖second‖
      simpa using (norm_inner_le_norm (𝕜 := Real) first second))

/-- The curried continuous bilinear form represented by `J†J`. -/
def shiftedCoefficientActionHessian
    (targetWeight : LatticeMode → Real) :
    ShiftedPotentialHilbert targetWeight →L[Real]
      ShiftedPotentialHilbert targetWeight →L[Real] Real :=
  (shiftedCoefficientRiesz targetWeight).comp
    (shiftedPullbackHessian targetWeight)

@[simp]
theorem shiftedCoefficientActionHessian_apply_apply
    (targetWeight : LatticeMode → Real)
    (first second : ShiftedPotentialHilbert targetWeight) :
    shiftedCoefficientActionHessian targetWeight first second =
      ⟪shiftedPullbackHessian targetWeight first, second⟫_Real := by
  rfl

/-- The first derivative is the Riesz functional represented by `J†J u`. -/
theorem shiftedCoefficientAction_hasFDerivAt
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    HasFDerivAt (shiftedCoefficientAction targetWeight)
      (shiftedCoefficientActionHessian targetWeight potential) potential := by
  let J := shiftedSobolevLorentzGram targetWeight
  have hJ : HasFDerivAt J J potential := J.hasFDerivAt
  have hInner := (hJ.inner Real hJ).const_mul (1 / 2 : Real)
  apply hInner.congr_fderiv
  ext direction
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    fderivInnerCLM_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply]
  change
    (1 / 2 : Real) *
        (⟪J potential, J direction⟫_Real +
          ⟪J direction, J potential⟫_Real) =
      ⟪shiftedPullbackHessian targetWeight potential, direction⟫_Real
  rw [shiftedPullbackHessian_pairing]
  rw [real_inner_comm (J direction) (J potential)]
  ring

theorem shiftedCoefficientAction_fderiv
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    fderiv Real (shiftedCoefficientAction targetWeight) potential =
      shiftedCoefficientActionHessian targetWeight potential :=
  (shiftedCoefficientAction_hasFDerivAt targetWeight potential).fderiv

/-- The genuine second Frechet derivative of the same coefficient action is
the continuous pullback Hessian `J†J`, at every base point. -/
theorem shiftedCoefficientAction_second_fderiv
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    fderiv Real
        (fun point =>
          fderiv Real (shiftedCoefficientAction targetWeight) point)
        potential =
      shiftedCoefficientActionHessian targetWeight := by
  have hFirstDerivative :
      (fun point =>
        fderiv Real (shiftedCoefficientAction targetWeight) point) =
        shiftedCoefficientActionHessian targetWeight := by
    funext point
    exact shiftedCoefficientAction_fderiv targetWeight point
  rw [hFirstDerivative]
  exact (shiftedCoefficientActionHessian targetWeight).hasFDerivAt.fderiv

theorem shiftedCoefficientAction_second_fderiv_pairing
    (targetWeight : LatticeMode → Real)
    (potential first second : ShiftedPotentialHilbert targetWeight) :
    fderiv Real
        (fun point =>
          fderiv Real (shiftedCoefficientAction targetWeight) point)
        potential first second =
      ⟪shiftedSobolevLorentzGram targetWeight first,
        shiftedSobolevLorentzGram targetWeight second⟫_Real := by
  rw [shiftedCoefficientAction_second_fderiv]
  exact shiftedPullbackHessian_pairing targetWeight first second

theorem shifted_sobolev_same_action_hessian_gate
    (targetWeight : LatticeMode → Real) :
    ∀ potential first second : ShiftedPotentialHilbert targetWeight,
      fderiv Real
          (fun point =>
            fderiv Real (shiftedCoefficientAction targetWeight) point)
          potential first second =
        ⟪shiftedSobolevLorentzGram targetWeight first,
          shiftedSobolevLorentzGram targetWeight second⟫_Real :=
  shiftedCoefficientAction_second_fderiv_pairing targetWeight

end

end P0EFTJanusShiftedSobolevSameActionHessian
end JanusFormal
