import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A variable bilinear coefficient is frozen at the origin in the second jet
when both argument fields are linear and vanish there. -/
namespace JanusFormal.P0EFTJanusProgramPT12BilinearSecondJetFreeze4D
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]

local instance : NormedAddCommGroup (G →L[Real] Real) := inferInstance
local instance : NormedSpace Real (G →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] G →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] G →L[Real] Real) := inferInstance

private theorem first_fderiv_apply
    (A : E → F →L[Real] G →L[Real] Real) (u : E →L[Real] F) (v : E →L[Real] G)
    (x b : E) (hA : DifferentiableAt Real A x) :
    fderiv Real (fun y => A y (u y) (v y)) x b =
      fderiv Real A x b (u x) (v x) + A x (u b) (v x) + A x (u x) (v b) := by
  rw [((hA.hasFDerivAt.clm_apply u.hasFDerivAt).clm_apply v.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    _root_.add_apply]
  ring

/-- The genuine Hessian uses only the value of the coefficient at zero. -/
theorem bilinearCoefficient_second_fderiv_zero
    (A : E → F →L[Real] G →L[Real] Real) (u : E →L[Real] F) (v : E →L[Real] G)
    (hA : ContDiffAt Real 2 A 0) (a b : E) :
    fderiv Real (fderiv Real (fun x => A x (u x) (v x))) 0 a b =
      A 0 (u a) (v b) + A 0 (u b) (v a) := by
  let f : E → Real := fun x => A x (u x) (v x)
  let gradientAtB : E → Real := fun x =>
    fderiv Real A x b (u x) (v x) + A x (u b) (v x) + A x (u x) (v b)
  have hNear : (fun x => fderiv Real f x b) =ᶠ[𝓝 (0 : E)] gradientAtB := by
    filter_upwards [hA.eventually (by norm_num)] with x hx
    exact first_fderiv_apply A u v x b (hx.differentiableAt (by norm_num))
  have hDA : DifferentiableAt Real (fderiv Real A) 0 :=
    (hA.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hAt := (hA.differentiableAt (by norm_num)).hasFDerivAt
  have hFirst := ((hDA.hasFDerivAt.clm_apply (hasFDerivAt_const b (0 : E))).clm_apply
    u.hasFDerivAt).clm_apply v.hasFDerivAt
  have hSecond := (hAt.clm_apply (hasFDerivAt_const (u b) (0 : E))).clm_apply v.hasFDerivAt
  have hThird := (hAt.clm_apply u.hasFDerivAt).clm_apply (hasFDerivAt_const (v b) (0 : E))
  have hSum := (hFirst.add hSecond).add hThird
  have hf : ContDiffAt Real 2 f 0 :=
    (hA.clm_apply u.contDiff.contDiffAt).clm_apply v.contDiff.contDiffAt
  have hDf : DifferentiableAt Real (fderiv Real f) 0 :=
    (hf.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hEvaluation := hDf.hasFDerivAt.clm_apply (hasFDerivAt_const b (0 : E))
  change fderiv Real (fderiv Real f) 0 a b = _
  calc
    fderiv Real (fderiv Real f) 0 a b =
        fderiv Real (fun x => fderiv Real f x b) 0 a := by
      rw [hEvaluation.fderiv]
      simp
    _ = fderiv Real gradientAtB 0 a :=
      congrArg (fun derivative : E →L[Real] Real => derivative a) hNear.fderiv_eq
    _ = A 0 (u a) (v b) + A 0 (u b) (v a) := by
      simpa [gradientAtB, Pi.add_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, add_comm] using
        congrArg (fun derivative : E →L[Real] Real => derivative a) hSum.fderiv

end
end JanusFormal.P0EFTJanusProgramPT12BilinearSecondJetFreeze4D
