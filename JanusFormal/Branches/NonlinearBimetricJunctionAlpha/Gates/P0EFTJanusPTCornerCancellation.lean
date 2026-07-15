import Mathlib

namespace JanusFormal
namespace P0EFTJanusPTCornerCancellation

set_option autoImplicit false

def cornerResidual (wPlus etaPlus wMinus etaMinus : ℝ) : ℝ :=
  wPlus * etaPlus + wMinus * etaMinus

theorem weighted_pt_corner_cancels
    (wPlus etaPlus wMinus etaMinus : ℝ)
    (hPT : wMinus * etaMinus = -(wPlus * etaPlus)) :
    cornerResidual wPlus etaPlus wMinus etaMinus = 0 := by
  unfold cornerResidual
  linarith

theorem opposite_rescaling_residual (wPlus wMinus lambda : ℝ) :
    cornerResidual wPlus lambda wMinus (-lambda) =
      (wPlus - wMinus) * lambda := by
  unfold cornerResidual
  ring

theorem equal_weight_rescaling_cancels (w lambda : ℝ) :
    cornerResidual w lambda w (-lambda) = 0 := by
  unfold cornerResidual
  ring

end P0EFTJanusPTCornerCancellation
end JanusFormal
