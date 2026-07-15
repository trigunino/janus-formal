import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFrechetPullbackSecondVariation

namespace JanusFormal
namespace P0EFTJanusFrechetPullbackHelmholtz

set_option autoImplicit false

noncomputable section

open P0EFTJanusFrechetPullbackSecondVariation

universe u v

variable {Source : Type u} {Target : Type v}
variable [NormedAddCommGroup Source] [NormedSpace ℝ Source]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target]

/-- The complete nonlinear pullback second variation satisfies genuine
Helmholtz reciprocity.  Unlike a purely algebraic `Jᵀ H J` argument, this
also covers the off-critical gradient--second-jet correction. -/
theorem sourceSecondVariation_symmetric
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (hTarget : Differentiable ℝ targetAction)
    (hMap : Differentiable ℝ compatibleMap)
    (x : Source)
    (secondJet : SourceSecondJet (Source := Source) (Target := Target))
    (targetHessian : TargetHessian (Target := Target))
    (hSecondJet :
      HasFDerivAt (fun y => fderiv ℝ compatibleMap y) secondJet x)
    (hTargetHessian :
      HasFDerivAt (fun z => fderiv ℝ targetAction z)
        targetHessian (compatibleMap x))
    (first second : Source) :
    sourceSecondVariation (fderiv ℝ compatibleMap x)
        (fderiv ℝ targetAction (compatibleMap x))
        targetHessian secondJet first second =
      sourceSecondVariation (fderiv ℝ compatibleMap x)
        (fderiv ℝ targetAction (compatibleMap x))
        targetHessian secondJet second first := by
  have hFirstDerivative :
      ∀ y, HasFDerivAt
        (pulledBackAction targetAction compatibleMap)
        (fderiv ℝ (pulledBackAction targetAction compatibleMap) y) y := by
    intro y
    rw [pulledBackAction_fderiv targetAction compatibleMap hTarget hMap y]
    exact pulledBackAction_hasFDerivAt targetAction compatibleMap y
      (fderiv ℝ targetAction (compatibleMap y))
      (fderiv ℝ compatibleMap y)
      (hTarget (compatibleMap y)).hasFDerivAt
      (hMap y).hasFDerivAt
  exact second_derivative_symmetric hFirstDerivative
    (pulledBackAction_fderiv_hasFDerivAt targetAction compatibleMap
      hTarget hMap x secondJet targetHessian hSecondJet hTargetHessian)
    first second

/-- At a target critical point, the actual critical pullback Hessian
`Jᵀ H J` is symmetric without separately postulating symmetry of `H`. -/
theorem jacobianPullbackHessian_symmetric_at_critical
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (hTarget : Differentiable ℝ targetAction)
    (hMap : Differentiable ℝ compatibleMap)
    (x : Source)
    (secondJet : SourceSecondJet (Source := Source) (Target := Target))
    (targetHessian : TargetHessian (Target := Target))
    (hSecondJet :
      HasFDerivAt (fun y => fderiv ℝ compatibleMap y) secondJet x)
    (hTargetHessian :
      HasFDerivAt (fun z => fderiv ℝ targetAction z)
        targetHessian (compatibleMap x))
    (hCritical : fderiv ℝ targetAction (compatibleMap x) = 0)
    (first second : Source) :
    jacobianPullbackHessian (fderiv ℝ compatibleMap x)
        targetHessian first second =
      jacobianPullbackHessian (fderiv ℝ compatibleMap x)
        targetHessian second first := by
  have hSymmetric := sourceSecondVariation_symmetric targetAction compatibleMap
    hTarget hMap x secondJet targetHessian hSecondJet hTargetHessian
    first second
  simpa [sourceSecondVariation_apply_apply, hCritical] using hSymmetric

end

end P0EFTJanusFrechetPullbackHelmholtz
end JanusFormal
