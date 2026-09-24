import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! The second derivative of a nonlinear chart retains the chart acceleration term. -/
namespace JanusFormal.P0EFTJanusProgramPT12NonlinearHessianPullback4D
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem nonlinearHessian (action : F → Real) (chart : E → F) (point first second : E)
    (hAction : ContDiffAt Real 2 action (chart point)) (hChart : ContDiffAt Real 2 chart point) :
    fderiv Real (fderiv Real (action ∘ chart)) point first second =
    fderiv Real (fderiv Real action) (chart point)
      (fderiv Real chart point first) (fderiv Real chart point second) +
    fderiv Real action (chart point) (fderiv Real (fderiv Real chart) point first second) := by
  have hChartOne := hChart.differentiableAt (by norm_num)
  have hNearChart := (hChart.eventually (by norm_num)).mono
    (fun _ h => h.differentiableAt (by norm_num))
  have hNearAction := hChartOne.continuousAt.eventually
    ((hAction.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num)))
  have hGradient : fderiv Real (action ∘ chart) =ᶠ[𝓝 point]
      (fun current => (fderiv Real action (chart current)).comp (fderiv Real chart current)) := by
    filter_upwards [hNearChart, hNearAction] with current hC hA
    exact (hA.hasFDerivAt.comp current hC.hasFDerivAt).fderiv
  have hActionTwo := (hAction.fderiv_right
    (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hChartTwo := (hChart.fderiv_right
    (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hDerivative := (hActionTwo.hasFDerivAt.comp point hChartOne.hasFDerivAt).clm_comp
    hChartTwo.hasFDerivAt
  simp only [Function.comp_def] at hDerivative
  rw [hGradient.fderiv_eq, hDerivative.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

end
end JanusFormal.P0EFTJanusProgramPT12NonlinearHessianPullback4D
