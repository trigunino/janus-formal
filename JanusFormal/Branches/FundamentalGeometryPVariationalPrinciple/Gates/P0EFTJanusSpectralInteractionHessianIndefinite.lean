import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitReciprocalCrossDensityFrechet

/-!
The elementary-symmetric interaction is multi-affine in its four eigenvalues.
Consequently its spectral Hessian has zero diagonal.  Whenever one mixed
coefficient is nonzero, two explicit eigenvalue directions have opposite
quadratic signs.

This is an interaction-only spectral-chart no-go.  It is not a ghost or
stability verdict for the constrained covariant bimetric theory, whose kinetic,
lapse/shift and gauge sectors are absent here.
-/

namespace JanusFormal
namespace P0EFTJanusSpectralInteractionHessianIndefinite

set_option autoImplicit false

noncomputable section

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusExplicitReciprocalCrossDensities
open P0EFTJanusExplicitReciprocalCrossDensityFrechet
open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- Equal variations of eigenvalues zero and one. -/
def pair01SameDirection : SquareRootSpectrum :=
  fun i => if i = 0 then 1 else if i = 1 then 1 else 0

/-- Opposite variations of eigenvalues zero and one. -/
def pair01OppositeDirection : SquareRootSpectrum :=
  fun i => if i = 0 then 1 else if i = 1 then -1 else 0

theorem spectralHessian_pair01_same
    (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) :
    spectralHessian coefficients spectrum pair01SameDirection
        pair01SameDirection =
      2 * mixedSecondCoefficient coefficients (spectrum 2) (spectrum 3) := by
  simp [spectralHessian, spectralHessianRow0, spectralHessianRow1,
    spectralHessianRow2, spectralHessianRow3, pair01SameDirection,
    spectrumCoordinate, smul_eq_mul]
  ring

theorem spectralHessian_pair01_opposite
    (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) :
    spectralHessian coefficients spectrum pair01OppositeDirection
        pair01OppositeDirection =
      -2 * mixedSecondCoefficient coefficients (spectrum 2) (spectrum 3) := by
  simp [spectralHessian, spectralHessianRow0, spectralHessianRow1,
    spectralHessianRow2, spectralHessianRow3, pair01OppositeDirection,
    spectrumCoordinate, smul_eq_mul]
  ring

/-- A nonzero mixed spectral coefficient forces both a positive and a negative
interaction-Hessian direction. -/
theorem nonzero_mixed01_forces_spectral_interaction_indefinite
    (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum)
    (hMixed :
      mixedSecondCoefficient coefficients (spectrum 2) (spectrum 3) ≠ 0) :
    (∃ direction,
        spectralHessian coefficients spectrum direction direction < 0) ∧
      (∃ direction,
        0 < spectralHessian coefficients spectrum direction direction) := by
  rcases lt_or_gt_of_ne hMixed with hNegative | hPositive
  · constructor
    · refine ⟨pair01SameDirection, ?_⟩
      rw [spectralHessian_pair01_same]
      linarith
    · refine ⟨pair01OppositeDirection, ?_⟩
      rw [spectralHessian_pair01_opposite]
      linarith
  · constructor
    · refine ⟨pair01OppositeDirection, ?_⟩
      rw [spectralHessian_pair01_opposite]
      linarith
    · refine ⟨pair01SameDirection, ?_⟩
      rw [spectralHessian_pair01_same]
      linarith

theorem nonzero_scale_mixed01_forces_common_interaction_indefinite
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum)
    (hScale : interactionScale ≠ 0)
    (hMixed :
      mixedSecondCoefficient coefficients (spectrum 2) (spectrum 3) ≠ 0) :
    (∃ direction,
        commonInteractionHessian interactionScale coefficients spectrum
          direction direction < 0) ∧
      (∃ direction,
        0 < commonInteractionHessian interactionScale coefficients spectrum
          direction direction) := by
  obtain ⟨⟨negativeDirection, hNegative⟩,
      ⟨positiveDirection, hPositive⟩⟩ :=
    nonzero_mixed01_forces_spectral_interaction_indefinite
      coefficients spectrum hMixed
  have hFactor : -interactionScale ≠ 0 := neg_ne_zero.mpr hScale
  rcases lt_or_gt_of_ne hFactor with hFactorNegative | hFactorPositive
  · constructor
    · refine ⟨positiveDirection, ?_⟩
      change (-interactionScale) *
        spectralHessian coefficients spectrum positiveDirection
          positiveDirection < 0
      nlinarith
    · refine ⟨negativeDirection, ?_⟩
      change 0 < (-interactionScale) *
        spectralHessian coefficients spectrum negativeDirection
          negativeDirection
      nlinarith
  · constructor
    · refine ⟨negativeDirection, ?_⟩
      change (-interactionScale) *
        spectralHessian coefficients spectrum negativeDirection
          negativeDirection < 0
      nlinarith
    · refine ⟨positiveDirection, ?_⟩
      change 0 < (-interactionScale) *
        spectralHessian coefficients spectrum positiveDirection
          positiveDirection
      nlinarith
/-- Therefore a strictly positive-semidefinite interaction Hessian must have
this mixed coefficient equal to zero. -/
theorem positiveSemidefinite_forces_mixed01_zero
    (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum)
    (hNonnegative : ∀ direction,
      0 ≤ spectralHessian coefficients spectrum direction direction) :
    mixedSecondCoefficient coefficients (spectrum 2) (spectrum 3) = 0 := by
  by_contra hMixed
  obtain ⟨direction, hNegative⟩ :=
    (nonzero_mixed01_forces_spectral_interaction_indefinite
      coefficients spectrum hMixed).1
  exact (not_lt_of_ge (hNonnegative direction)) hNegative

theorem ptFlat_symmetric_mixed01
    (beta1 beta2 : ℝ) :
    mixedSecondCoefficient (ptFlatCoefficients beta1 beta2)
        ((proportionalSpectrum 1) 2) ((proportionalSpectrum 1) 3) =
      -2 * (beta1 + beta2) := by
  simp [mixedSecondCoefficient, ptFlatCoefficients, proportionalSpectrum]
  ring

/-- The cone with positive reduced proportional curvature still has an
indefinite interaction-only Hessian in the full eigenvalue chart. -/
theorem positive_ptFlat_cone_spectral_interaction_indefinite
    (beta1 beta2 : ℝ) (hBeta1 : 0 < beta1) (hBeta2 : 0 ≤ beta2) :
    (∃ direction,
        spectralHessian (ptFlatCoefficients beta1 beta2)
          (proportionalSpectrum 1) direction direction < 0) ∧
      (∃ direction,
        0 < spectralHessian (ptFlatCoefficients beta1 beta2)
          (proportionalSpectrum 1) direction direction) := by
  apply nonzero_mixed01_forces_spectral_interaction_indefinite
  rw [ptFlat_symmetric_mixed01]
  nlinarith

end

end P0EFTJanusSpectralInteractionHessianIndefinite
end JanusFormal
