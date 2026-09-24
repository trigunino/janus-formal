import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Second derivatives of a continuous bilinear pairing, with all four terms. -/
namespace JanusFormal.P0EFTJanusProgramPT12BilinearHessian4D
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]
  [NormedAddCommGroup H] [NormedSpace Real H]

theorem bilinearHessian (pairing : F →L[Real] G →L[Real] H)
    (left : E → F) (right : E → G) (point first second : E)
    (hLeft : ContDiffAt Real 2 left point) (hRight : ContDiffAt Real 2 right point) :
    fderiv Real (fderiv Real (fun current => pairing (left current) (right current)))
      point first second =
      pairing (left point) (fderiv Real (fderiv Real right) point first second) +
      pairing (fderiv Real left point first) (fderiv Real right point second) +
      (pairing (fderiv Real (fderiv Real left) point first second) (right point) +
      pairing (fderiv Real left point second) (fderiv Real right point first)) := by
  have hLeftOne := hLeft.differentiableAt (by norm_num)
  have hRightOne := hRight.differentiableAt (by norm_num)
  have hNearLeft := (hLeft.eventually (by norm_num)).mono
    (fun _ h => h.differentiableAt (by norm_num))
  have hNearRight := (hRight.eventually (by norm_num)).mono
    (fun _ h => h.differentiableAt (by norm_num))
  have hGradient : fderiv Real (fun current => pairing (left current) (right current)) =ᶠ[𝓝 point]
      (fun current => (pairing (left current)).comp (fderiv Real right current) +
        (pairing.flip (right current)).comp (fderiv Real left current)) := by
    filter_upwards [hNearLeft, hNearRight] with current hL hR
    exact ((pairing.hasFDerivAt.comp current hL.hasFDerivAt).clm_apply hR.hasFDerivAt).fderiv
  have hLeftTwo := (hLeft.fderiv_right
    (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hRightTwo := (hRight.fderiv_right
    (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hDerivative := ((pairing.hasFDerivAt.comp point hLeftOne.hasFDerivAt).clm_comp
      hRightTwo.hasFDerivAt).add
    ((pairing.flip.hasFDerivAt.comp point hRightOne.hasFDerivAt).clm_comp hLeftTwo.hasFDerivAt)
  simp only [Function.comp_def, Pi.add_def] at hDerivative
  rw [hGradient.fderiv_eq, hDerivative.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12BilinearHessian4D
