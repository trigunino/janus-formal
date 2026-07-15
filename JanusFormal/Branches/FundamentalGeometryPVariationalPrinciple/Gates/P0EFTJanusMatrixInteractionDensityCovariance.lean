import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixDiagonalGaugeNoether

/-!
Finite-matrix density covariance of the explicit interaction.

An arbitrary invertible simultaneous frame changes the metric volume factor
by `|det Q|`, while the interaction scalar is unchanged by the induced root
similarity.  Multiplication by the inverse-frame Jacobian therefore restores
the original scalar-density representative.

This is a pointwise matrix statement.  It does not construct a manifold
coordinate action, a spacetime integral, or a covariant Bianchi identity.
-/

namespace JanusFormal
namespace P0EFTJanusMatrixInteractionDensityCovariance

set_option autoImplicit false

noncomputable section

open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusReciprocalBimetricPotential

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

/-- The metric coordinate-volume factor has density weight one under an
arbitrary simultaneous frame congruence.  Invertibility is not needed for
this determinant identity itself. -/
theorem metricVolume_diagonal_weight
    (frame metric : Matrix4) :
    Real.sqrt |Matrix.det (metricCongruence frame metric)| =
      |Matrix.det frame| * Real.sqrt |Matrix.det metric| := by
  rw [det_metricCongruence, abs_mul, abs_pow,
    Real.sqrt_mul (sq_nonneg |Matrix.det frame|),
    Real.sqrt_sq (abs_nonneg (Matrix.det frame))]

/-- An explicit inverse witness forces the frame determinant to be nonzero. -/
theorem frame_det_ne_zero
    (frame inverse : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    Matrix.det frame ≠ 0 := by
  intro hZero
  have hDet := congrArg Matrix.det hFrame.mul_inverse
  rw [Matrix.det_mul, Matrix.det_one, hZero, zero_mul] at hDet
  exact zero_ne_one hDet

/-- The determinant of the supplied inverse is the reciprocal Jacobian
weight. -/
theorem abs_det_inverse_eq_inv_abs_det_frame
    (frame inverse : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    |Matrix.det inverse| = |Matrix.det frame|⁻¹ := by
  have hDet := congrArg Matrix.det hFrame.inverse_mul
  rw [Matrix.det_mul, Matrix.det_one] at hDet
  have hFrameDet : |Matrix.det frame| ≠ 0 :=
    abs_ne_zero.mpr (frame_det_ne_zero frame inverse hFrame)
  apply (mul_eq_one_iff_eq_inv₀ hFrameDet).1
  simpa [abs_mul] using congrArg abs hDet

/-- The explicit interaction coordinate density transforms with weight one
under every invertible simultaneous frame. -/
theorem pointwiseInteractionDensity_diagonal_weight
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (frame inverse : Matrix4)
    (hFrame : FrameInverseWitness frame inverse)
    (data : PointwiseBimetricRootData) :
    pointwiseInteractionDensity interactionScale coefficients
        (diagonalFrameAction frame inverse hFrame data) =
      |Matrix.det frame| *
        pointwiseInteractionDensity interactionScale coefficients data := by
  unfold pointwiseInteractionDensity
  change -interactionScale *
      Real.sqrt |Matrix.det (metricCongruence frame data.plusMetric)| *
        pointwiseInteractionScalar coefficients
          (diagonalFrameAction frame inverse hFrame data) =
    |Matrix.det frame| *
      (-interactionScale * Real.sqrt |Matrix.det data.plusMetric| *
        pointwiseInteractionScalar coefficients data)
  rw [metricVolume_diagonal_weight,
    pointwiseInteractionScalar_diagonal_invariant coefficients frame inverse
      hFrame data]
  ring

/-- Multiplying the transformed density by the inverse-coordinate Jacobian
recovers the original pointwise scalar-density representative. -/
theorem pointwiseInteractionDensity_inverseJacobian_compensated
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (frame inverse : Matrix4)
    (hFrame : FrameInverseWitness frame inverse)
    (data : PointwiseBimetricRootData) :
    |Matrix.det inverse| *
        pointwiseInteractionDensity interactionScale coefficients
          (diagonalFrameAction frame inverse hFrame data) =
      pointwiseInteractionDensity interactionScale coefficients data := by
  rw [pointwiseInteractionDensity_diagonal_weight interactionScale coefficients
    frame inverse hFrame data,
    abs_det_inverse_eq_inv_abs_det_frame frame inverse hFrame]
  field_simp [abs_ne_zero.mpr (frame_det_ne_zero frame inverse hFrame)]

end

end P0EFTJanusMatrixInteractionDensityCovariance
end JanusFormal
