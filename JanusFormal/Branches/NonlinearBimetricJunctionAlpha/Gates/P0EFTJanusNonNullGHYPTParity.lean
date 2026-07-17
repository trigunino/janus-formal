import Mathlib

namespace JanusFormal
namespace P0EFTJanusNonNullGHYPTParity

set_option autoImplicit false

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

end P0EFTJanusNonNullGHYPTParity
end JanusFormal
