import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Exact second derivatives under a scaled affine change of variables. -/
namespace JanusFormal.P0EFTJanusProgramPT12AffineHessianPullback4D
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem scaledAffineHessian (action : F → Real) (base : F) (projection : E →L[Real] F)
    (scale : Real) (hC2 : ContDiffAt Real 2 action base) (first second : E) :
    fderiv Real (fderiv Real (fun point => scale * action (base + projection point)))
      0 first second =
      scale * fderiv Real (fderiv Real action) base (projection first) (projection second) := by
  have hInput (point : E) : HasFDerivAt (fun y => base + projection y) projection point := by
    simpa only [Pi.add_def, zero_add] using
      (hasFDerivAt_const base point).add projection.hasFDerivAt
  have hNear : ∀ᶠ point in 𝓝 (0 : E), DifferentiableAt Real action (base + projection point) := by
    have h := (hC2.eventually (by norm_num)).mono (fun point hPoint => hPoint.differentiableAt (by norm_num))
    have ht : Tendsto (fun point : E => base + projection point) (𝓝 0) (𝓝 base) :=
      by simpa only [ContinuousAt, map_zero, add_zero] using (hInput (0 : E)).continuousAt
    exact ht.eventually h
  have hGradient :
      fderiv Real (fun point => scale * action (base + projection point)) =ᶠ[𝓝 (0 : E)]
      (fun point => scale • (fderiv Real action (base + projection point)).comp projection) := by
    filter_upwards [hNear] with point hPoint
    exact ((hPoint.hasFDerivAt.comp point (hInput point)).const_mul scale).fderiv
  have hSecond : DifferentiableAt Real (fderiv Real action) base :=
    (hC2.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hAtInput : HasFDerivAt (fderiv Real action) (fderiv Real (fderiv Real action) base)
      (base + projection 0) := by simpa only [map_zero, add_zero] using hSecond.hasFDerivAt
  have hDerivative := (((hAtInput.comp (0 : E) (hInput 0)).clm_comp
    (hasFDerivAt_const projection (0 : E))).const_smul scale)
  simp only [Function.comp_def, Pi.smul_def] at hDerivative
  rw [hGradient.fderiv_eq, hDerivative.fderiv]
  simp only [smul_apply, smul_eq_mul, add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, add_zero, zero_add, ContinuousLinearMap.flip_apply]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12AffineHessianPullback4D
