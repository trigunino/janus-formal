import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! An actual joint Hessian entry from differentiation of a metric partial derivative. -/
namespace JanusFormal.P0EFTJanusProgramPT12MixedPartialHessian4D
set_option autoImplicit false
noncomputable section
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup G] [NormedSpace Real G]
variable (action : E × G → Real)

theorem metricPartial_fderiv (g : G) (h : E)
    (hDiff : DifferentiableAt Real action (0, g)) :
    fderiv Real (fun x => action (x, g)) 0 h = fderiv Real action (0, g) (h, 0) := by
  have hMetric := hDiff.hasFDerivAt.comp (0 : E)
    (hasFDerivAt_prodMk_left (𝕜 := Real) (0 : E) g)
  simp only [Function.comp_def] at hMetric
  rw [hMetric.fderiv]
  rfl

theorem metricPartial_hasDerivAt (g v : G) (h : E)
    (hDiff : ∀ current : G, DifferentiableAt Real action (0, current))
    (hSecond : DifferentiableAt Real (fderiv Real action) (0, g)) :
    HasDerivAt (fun t : Real => fderiv Real (fun x => action (x, g + t • v)) 0 h)
      (fderiv Real (fderiv Real action) (0, g) (0, v) (h, 0)) 0 := by
  have hEval := hSecond.hasFDerivAt.clm_apply (hasFDerivAt_const (h, (0 : G)) ((0 : E), g))
  have hCurve : HasDerivAt (fun t : Real => ((0 : E), g + t • v)) ((0 : E), v) 0 := by
    simpa using (hasDerivAt_const (0 : Real) (0 : E)).prodMk
      (((hasDerivAt_id (0 : Real)).smul_const v).const_add g)
  have hEvalAt : HasFDerivAt (fun y => fderiv Real action y (h, 0))
      (fderiv Real action (0, g) ∘L 0 + (fderiv Real (fderiv Real action) (0, g)).flip (h, 0))
      ((0 : E), g + (0 : Real) • v) := by simpa using hEval
  have h := hEvalAt.comp_hasDerivAt 0 hCurve
  simpa only [metricPartial_fderiv action _ _ (hDiff _), Function.comp_def,
    zero_apply, add_apply, map_zero, ContinuousLinearMap.flip_apply, zero_add, ContinuousLinearMap.comp_apply] using h

end
end JanusFormal.P0EFTJanusProgramPT12MixedPartialHessian4D
