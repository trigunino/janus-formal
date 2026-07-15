import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedTwoMetricBoundaryFirstVariation

/-!
The additive diagonal translation of the two reduced scale variables is often
used as a Noether proxy.  This file applies that proxy to the actual explicit
reduced action and determines exactly when it is an infinitesimal symmetry.
No map from this reduced translation to a spacetime diagonal diffeomorphism is
assumed or proved.
-/

namespace JanusFormal
namespace P0EFTJanusReducedTwoMetricActionDiagonalNoetherAudit

set_option autoImplicit false

noncomputable section

open P0EFTJanusReducedTwoMetricBoundaryFirstVariation

/-- Additive diagonal line through a two-scale configuration. -/
def diagonalTranslation (scale : ScalePair) (t : ℝ) : ScalePair :=
  affineVariation scale (1, 1) t

/-- Euler contraction seen by the diagonal reduced direction. -/
def diagonalEuler
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ)
    (scale : ScalePair) : ℝ :=
  reducedEulerPlus bulkPlus coupling beta1 beta2 boundaryPlus scale +
    reducedEulerMinus bulkMinus coupling beta1 beta2 boundaryMinus scale

/-- The displayed diagonal Euler contraction is the genuine derivative of the
explicit reduced action along the additive diagonal line. -/
theorem reducedTwoMetricAction_diagonalTranslation_hasDerivAt
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ)
    (scale : ScalePair) :
    HasDerivAt
      (fun t => reducedTwoMetricAction bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus (diagonalTranslation scale t))
      (diagonalEuler bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus scale) 0 := by
  simpa [diagonalTranslation, diagonalEuler, pairFirstVariation] using
    reducedTwoMetricAction_line_hasDerivAt
      bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus
      scale (1, 1)

/-- Exact polynomial formula for the diagonal contraction. -/
theorem diagonalEuler_formula
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ)
    (scale : ScalePair) :
    diagonalEuler bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus scale =
      bulkPlus * scale.1 + bulkMinus * scale.2 +
        12 * coupling * (beta1 + beta2) *
          (scale.2 - scale.1) ^ 2 * (scale.1 + scale.2) +
        boundaryPlus + boundaryMinus := by
  rcases scale with ⟨scalePlus, scaleMinus⟩
  unfold diagonalEuler reducedEulerPlus reducedEulerMinus
    interactionEulerPlus interactionEulerMinus
    homogeneousRelativeShapePlus homogeneousRelativeShapeMinus
  ring

/-- Infinitesimal invariance of the explicit action under every additive
diagonal translation. -/
def AdditivelyDiagonalInvariant
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ) :
    Prop :=
  ∀ scale, HasDerivAt
    (fun t => reducedTwoMetricAction bulkPlus bulkMinus coupling beta1 beta2
      boundaryPlus boundaryMinus (diagonalTranslation scale t)) 0 0

theorem additivelyDiagonalInvariant_iff_diagonalEuler_zero
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ) :
    AdditivelyDiagonalInvariant bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus ↔
      ∀ scale, diagonalEuler bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus scale = 0 := by
  constructor
  · intro hInvariant scale
    exact (reducedTwoMetricAction_diagonalTranslation_hasDerivAt
      bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus
      scale).unique (hInvariant scale)
  · intro hEuler scale
    exact (reducedTwoMetricAction_diagonalTranslation_hasDerivAt
      bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus
      scale).congr_deriv (hEuler scale)

/-- Complete classification: the additive proxy is a symmetry only when both
bulk coefficients vanish, the cubic diagonal interaction contraction vanishes,
and the two linear boundary coefficients cancel. -/
theorem additivelyDiagonalInvariant_iff_coefficients
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ) :
    AdditivelyDiagonalInvariant bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus ↔
      bulkPlus = 0 ∧ bulkMinus = 0 ∧
        coupling * (beta1 + beta2) = 0 ∧
        boundaryPlus + boundaryMinus = 0 := by
  rw [additivelyDiagonalInvariant_iff_diagonalEuler_zero]
  constructor
  · intro hEuler
    have h00 := hEuler (0, 0)
    have h11 := hEuler (1, 1)
    have h1m1 := hEuler (1, -1)
    have h01 := hEuler (0, 1)
    rw [diagonalEuler_formula] at h00 h11 h1m1 h01
    norm_num at h00 h11 h1m1 h01
    have hBulkPlus : bulkPlus = 0 := by linarith
    have hBulkMinus : bulkMinus = 0 := by linarith
    have hInteraction : coupling * (beta1 + beta2) = 0 := by
      linarith [h00, h01]
    exact ⟨hBulkPlus, hBulkMinus, hInteraction, h00⟩
  · rintro ⟨hBulkPlus, hBulkMinus, hInteraction, hBoundary⟩ scale
    rw [diagonalEuler_formula, hBulkPlus, hBulkMinus]
    have hCubic : 12 * coupling * (beta1 + beta2) = 0 := by
      nlinarith
    rw [hCubic]
    simpa using hBoundary

/-- In the simplest positive interaction cone the additive diagonal line is
not a symmetry, even with zero reduced bulk and boundary coefficients. -/
theorem positive_interaction_not_additivelyDiagonalInvariant :
    ¬ AdditivelyDiagonalInvariant 0 0 1 1 0 0 0 := by
  rw [additivelyDiagonalInvariant_iff_coefficients]
  norm_num

/-- Concrete failure witnessed inside the strictly positive scale cone. -/
theorem positive_interaction_diagonal_derivative_at_positive_asymmetric_scale :
    HasDerivAt
      (fun t => reducedTwoMetricAction 0 0 1 1 0 0 0
        (diagonalTranslation (1, 2) t)) 36 0 := by
  convert reducedTwoMetricAction_diagonalTranslation_hasDerivAt
    0 0 1 1 0 0 0 (1, 2) using 1
  norm_num [diagonalEuler_formula]

/- The additive translation audited here changes homogeneous scale data. Its
failure is not a failure of diagonal spacetime diffeomorphism invariance; any
identification of the two transformations would require a separate bridge. -/

end

end P0EFTJanusReducedTwoMetricActionDiagonalNoetherAudit
end JanusFormal
