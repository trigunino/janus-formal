import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Second derivatives under affine input and continuous linear output maps. -/
namespace JanusFormal.P0EFTJanusProgramPT12VectorHessianPullback4D
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]

theorem affineHessian (field : F → G) (base : F) (projection : E →L[Real] F)
    (hC2 : ContDiffAt Real 2 field base) (first second : E) :
    fderiv Real (fderiv Real (fun point => field (base + projection point)))
      0 first second =
      fderiv Real (fderiv Real field) base (projection first) (projection second) := by
  have hInput (point : E) : HasFDerivAt (fun y => base + projection y) projection point := by
    simpa only [Pi.add_def, zero_add] using
      (hasFDerivAt_const base point).add projection.hasFDerivAt
  have hNear : ∀ᶠ point in 𝓝 (0 : E), DifferentiableAt Real field (base + projection point) := by
    have h := (hC2.eventually (by norm_num)).mono
      (fun point hPoint => hPoint.differentiableAt (by norm_num))
    have ht : Tendsto (fun point : E => base + projection point) (𝓝 0) (𝓝 base) :=
      by simpa only [ContinuousAt, map_zero, add_zero] using (hInput (0 : E)).continuousAt
    exact ht.eventually h
  have hGradient : fderiv Real (fun point => field (base + projection point)) =ᶠ[𝓝 (0 : E)]
      (fun point => (fderiv Real field (base + projection point)).comp projection) := by
    filter_upwards [hNear] with point hPoint
    exact (hPoint.hasFDerivAt.comp point (hInput point)).fderiv
  have hSecond := (hC2.fderiv_right
    (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hAtInput : HasFDerivAt (fderiv Real field) (fderiv Real (fderiv Real field) base)
      (base + projection 0) := by simpa only [map_zero, add_zero] using hSecond.hasFDerivAt
  have hDerivative := (hAtInput.comp (0 : E) (hInput 0)).clm_comp
    (hasFDerivAt_const projection (0 : E))
  simp only [Function.comp_def] at hDerivative
  rw [hGradient.fderiv_eq, hDerivative.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero,
    zero_add, ContinuousLinearMap.flip_apply]
  rfl

theorem linearPostHessian (linear : F →L[Real] G) (field : E → F)
    (point first second : E) (hC2 : ContDiffAt Real 2 field point) :
    fderiv Real (fderiv Real (linear ∘ field)) point first second =
      linear (fderiv Real (fderiv Real field) point first second) := by
  have hNear := (hC2.eventually (by norm_num)).mono
    (fun _ h => h.differentiableAt (by norm_num))
  have hGradient : fderiv Real (linear ∘ field) =ᶠ[𝓝 point]
      (fun current => linear.comp (fderiv Real field current)) := by
    filter_upwards [hNear] with current hCurrent
    exact (linear.hasFDerivAt.comp current hCurrent.hasFDerivAt).fderiv
  have hSecond := (hC2.fderiv_right
    (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hDerivative := (hasFDerivAt_const linear point).clm_comp hSecond.hasFDerivAt
  rw [hGradient.fderiv_eq, hDerivative.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero,
    add_zero]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12VectorHessianPullback4D
