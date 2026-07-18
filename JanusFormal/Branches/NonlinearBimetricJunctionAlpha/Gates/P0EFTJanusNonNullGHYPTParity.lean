import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussianNormalEmbeddedHypersurface
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D

namespace JanusFormal
namespace P0EFTJanusNonNullGHYPTParity

set_option autoImplicit false

open P0EFTJanusGaussianNormalEmbeddedHypersurface

def pairedFactor (scaleRatio orientationParity curvatureParity : ℝ) : ℝ :=
  1 + scaleRatio * orientationParity * curvatureParity

theorem double_sign_reversal_is_even (scaleRatio : ℝ) :
    pairedFactor scaleRatio (-1) (-1) = 1 + scaleRatio := by
  unfold pairedFactor
  ring

theorem one_sign_reversal_cancels_equal_scales :
    pairedFactor 1 (-1) 1 = 0 ∧ pairedFactor 1 1 (-1) = 0 := by
  unfold pairedFactor
  constructor <;> ring

theorem cancellation_condition
    (scaleRatio orientationParity curvatureParity : ℝ) :
    pairedFactor scaleRatio orientationParity curvatureParity = 0 ↔
      scaleRatio * orientationParity * curvatureParity = -1 := by
  unfold pairedFactor
  constructor <;> intro h <;> linarith

theorem pt_fixed_odd_tensor_vanishes
    (K : Matrix (Fin 3) (Fin 3) ℝ) (hOdd : K = -K) : K = 0 := by
  ext row column
  have hEntry := congrArg (fun A => A row column) hOdd
  simp only [Matrix.neg_apply, Matrix.zero_apply] at hEntry ⊢
  linarith

theorem sign_clutched_ghy_density_descends
    (transition orientation meanCurvature : ℝ)
    (hSign : transition ^ 2 = 1) :
    (transition * orientation) * (transition * meanCurvature) =
      orientation * meanCurvature := by
  calc
    (transition * orientation) * (transition * meanCurvature) =
        transition ^ 2 * (orientation * meanCurvature) := by ring
    _ = orientation * meanCurvature := by rw [hSign, one_mul]

theorem gaussian_secondFundamental_orientation_reversal
    (convention : SecondFundamentalConvention)
    (data : GaussianAffineData) :
    secondFundamentalForm convention data .decreasing =
      -secondFundamentalForm convention data .increasing := by
  ext row column
  change secondFundamentalForm convention data .decreasing row column =
    -(secondFundamentalForm convention data .increasing row column)
  rw [secondFundamentalForm_eq, secondFundamentalForm_eq]
  simp [NormalOrientation.sign]

theorem gaussian_extrinsicTrace_orientation_reversal
    (convention : SecondFundamentalConvention)
    (data : GaussianAffineData) :
    extrinsicTrace convention data .decreasing =
      -extrinsicTrace convention data .increasing := by
  rw [extrinsicTrace_eq, extrinsicTrace_eq]
  simp [NormalOrientation.sign]

theorem equatorialWarpDerivative_zero :
    (-2 : ℝ) * Real.sin 0 * Real.cos 0 = 0 := by
  norm_num

end P0EFTJanusNonNullGHYPTParity
end JanusFormal
