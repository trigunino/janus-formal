import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Differentiating the actual gradient pulled back by a continuous linear projection. -/
namespace JanusFormal.P0EFTJanusProgramPT12ProjectedGradientDerivative4D
set_option autoImplicit false
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem projectedGradient_fderiv (action : F → Real) (projection : E →L[Real] F)
    (hSecond : DifferentiableAt Real (fderiv Real action) 0) (first second : E) :
    fderiv Real (fun point => (fderiv Real action (projection point)).comp projection)
      0 first second =
    fderiv Real (fderiv Real action) 0 (projection first) (projection second) := by
  have hAtInput : HasFDerivAt (fderiv Real action)
      (fderiv Real (fderiv Real action) 0) (projection 0) := by
    simpa only [map_zero] using hSecond.hasFDerivAt
  have hDerivative := (hAtInput.comp (0 : E) projection.hasFDerivAt).clm_comp
    (hasFDerivAt_const projection (0 : E))
  simp only [Function.comp_def] at hDerivative
  rw [hDerivative.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero,
    zero_add, ContinuousLinearMap.flip_apply]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12ProjectedGradientDerivative4D
