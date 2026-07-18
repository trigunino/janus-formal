import Mathlib.Analysis.InnerProductSpace.Adjoint
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevLatticeLorentzGram

/-!
# Target pairing and pullback Hessian on the shifted lattice-Sobolev complex

The target metric coefficient Hilbert space carries its canonical positive
identity Hessian.  Pulling it back through the bounded shifted Lorentz--Gram
operator gives the actual continuous operator `J† J`.  Its bilinear form is
the target inner product, hence symmetric and nonnegative, and its kernel is
exactly the kernel of `J`.

This is the `Z^4` coefficient model only.  It is not the Hessian of the full
nonlinear global Janus action.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedSobolevPullbackHessian

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusLatticeFourierSaintVenantExactness
open P0EFTJanusWeightedL2LatticeSaintVenantExactness
open P0EFTJanusShiftedSobolevLatticeLorentzGram

/-- Canonical continuous self-adjoint target pairing. -/
def targetIdentityHessian
    (targetWeight : LatticeMode → Real) :
    SobolevMetricHilbert targetWeight →L[Real]
      SobolevMetricHilbert targetWeight :=
  ContinuousLinearMap.id Real _

@[simp]
theorem targetIdentityHessian_apply
    (targetWeight : LatticeMode → Real)
    (tensor : SobolevMetricHilbert targetWeight) :
    targetIdentityHessian targetWeight tensor = tensor := rfl

theorem targetIdentityHessian_selfAdjoint_pairing
    (targetWeight : LatticeMode → Real)
    (first second : SobolevMetricHilbert targetWeight) :
    ⟪targetIdentityHessian targetWeight first, second⟫_Real =
      ⟪first, targetIdentityHessian targetWeight second⟫_Real := by
  rfl

theorem targetIdentityHessian_nonnegative
    (targetWeight : LatticeMode → Real)
    (tensor : SobolevMetricHilbert targetWeight) :
    0 ≤ ⟪targetIdentityHessian targetWeight tensor, tensor⟫_Real := by
  exact real_inner_self_nonneg

/-- Actual continuous pullback `J† H J` with `H = id`. -/
def shiftedPullbackHessian
    (targetWeight : LatticeMode → Real) :
    ShiftedPotentialHilbert targetWeight →L[Real]
      ShiftedPotentialHilbert targetWeight :=
  (ContinuousLinearMap.adjoint
      (shiftedSobolevLorentzGram targetWeight)).comp
    ((targetIdentityHessian targetWeight).comp
      (shiftedSobolevLorentzGram targetWeight))

theorem shiftedPullbackHessian_pairing
    (targetWeight : LatticeMode → Real)
    (first second : ShiftedPotentialHilbert targetWeight) :
    ⟪shiftedPullbackHessian targetWeight first, second⟫_Real =
      ⟪shiftedSobolevLorentzGram targetWeight first,
        shiftedSobolevLorentzGram targetWeight second⟫_Real := by
  change
    ⟪ContinuousLinearMap.adjoint
        (shiftedSobolevLorentzGram targetWeight)
        (shiftedSobolevLorentzGram targetWeight first), second⟫_Real =
      ⟪shiftedSobolevLorentzGram targetWeight first,
        shiftedSobolevLorentzGram targetWeight second⟫_Real
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

theorem shiftedPullbackHessian_symmetric
    (targetWeight : LatticeMode → Real)
    (first second : ShiftedPotentialHilbert targetWeight) :
    ⟪shiftedPullbackHessian targetWeight first, second⟫_Real =
      ⟪first, shiftedPullbackHessian targetWeight second⟫_Real := by
  calc
    ⟪shiftedPullbackHessian targetWeight first, second⟫_Real =
        ⟪shiftedSobolevLorentzGram targetWeight first,
          shiftedSobolevLorentzGram targetWeight second⟫_Real :=
      shiftedPullbackHessian_pairing targetWeight first second
    _ = ⟪shiftedSobolevLorentzGram targetWeight second,
          shiftedSobolevLorentzGram targetWeight first⟫_Real :=
      (real_inner_comm _ _).symm
    _ = ⟪shiftedPullbackHessian targetWeight second, first⟫_Real :=
      (shiftedPullbackHessian_pairing targetWeight second first).symm
    _ = ⟪first, shiftedPullbackHessian targetWeight second⟫_Real :=
      (real_inner_comm _ _).symm

theorem shiftedPullbackHessian_nonnegative
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    0 ≤ ⟪shiftedPullbackHessian targetWeight potential, potential⟫_Real := by
  rw [shiftedPullbackHessian_pairing]
  exact real_inner_self_nonneg

theorem shiftedPullbackHessian_quadratic_eq_norm_sq
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    ⟪shiftedPullbackHessian targetWeight potential, potential⟫_Real =
      ‖shiftedSobolevLorentzGram targetWeight potential‖ ^ 2 := by
  rw [shiftedPullbackHessian_pairing]
  exact real_inner_self_eq_norm_sq _

theorem shiftedPullbackHessian_apply_eq_zero_iff
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    shiftedPullbackHessian targetWeight potential = 0 ↔
      shiftedSobolevLorentzGram targetWeight potential = 0 := by
  constructor
  · intro hPullback
    have hPairing :
        ⟪shiftedPullbackHessian targetWeight potential, potential⟫_Real = 0 := by
      simp [hPullback]
    rw [shiftedPullbackHessian_quadratic_eq_norm_sq] at hPairing
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hPairing)
  · intro hSymbol
    apply ext_inner_right Real
    intro test
    rw [shiftedPullbackHessian_pairing, hSymbol]
    simp

theorem shiftedPullbackHessian_apply_eq_zero_iff_zeroModeSupport
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    shiftedPullbackHessian targetWeight potential = 0 ↔
      ∀ mode : LatticeMode, mode ≠ 0 → potential mode = 0 := by
  rw [shiftedPullbackHessian_apply_eq_zero_iff]
  exact shiftedSobolevLorentzGram_eq_zero_iff targetWeight potential

/-- Removing the finite zero mode makes the pullback quadratic form positive
definite. -/
theorem shiftedPullbackHessian_positiveDefinite_of_zeroModeFree
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight)
    (hZeroMode : potential 0 = 0) :
    ⟪shiftedPullbackHessian targetWeight potential, potential⟫_Real = 0 ↔
      potential = 0 := by
  constructor
  · intro hQuadratic
    rw [shiftedPullbackHessian_quadratic_eq_norm_sq] at hQuadratic
    have hSymbol : shiftedSobolevLorentzGram targetWeight potential = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hQuadratic)
    have hModes :=
      (shiftedSobolevLorentzGram_eq_zero_iff targetWeight potential).mp hSymbol
    apply Subtype.ext
    funext mode
    by_cases hMode : mode = 0
    · subst mode
      simpa using hZeroMode
    · simpa using hModes mode hMode
  · rintro rfl
    simp

theorem shifted_pullback_hessian_gate
    (targetWeight : LatticeMode → Real) :
    (∀ first second : ShiftedPotentialHilbert targetWeight,
      ⟪shiftedPullbackHessian targetWeight first, second⟫_Real =
        ⟪first, shiftedPullbackHessian targetWeight second⟫_Real) ∧
    (∀ potential : ShiftedPotentialHilbert targetWeight,
      0 ≤ ⟪shiftedPullbackHessian targetWeight potential, potential⟫_Real) ∧
    (∀ potential : ShiftedPotentialHilbert targetWeight,
      shiftedPullbackHessian targetWeight potential = 0 ↔
        shiftedSobolevLorentzGram targetWeight potential = 0) ∧
    (∀ potential : ShiftedPotentialHilbert targetWeight,
      potential 0 = 0 →
      (⟪shiftedPullbackHessian targetWeight potential, potential⟫_Real = 0 ↔
        potential = 0)) := by
  exact ⟨shiftedPullbackHessian_symmetric targetWeight,
    shiftedPullbackHessian_nonnegative targetWeight,
    shiftedPullbackHessian_apply_eq_zero_iff targetWeight,
    shiftedPullbackHessian_positiveDefinite_of_zeroModeFree targetWeight⟩

end

end P0EFTJanusShiftedSobolevPullbackHessian
end JanusFormal
