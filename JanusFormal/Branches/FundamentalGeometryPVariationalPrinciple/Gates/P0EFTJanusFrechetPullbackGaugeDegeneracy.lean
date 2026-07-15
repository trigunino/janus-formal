import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFrechetPullbackHelmholtz

namespace JanusFormal
namespace P0EFTJanusFrechetPullbackGaugeDegeneracy

set_option autoImplicit false

noncomputable section

open P0EFTJanusFrechetPullbackSecondVariation
open P0EFTJanusFrechetPullbackHelmholtz

universe u v w

variable {Source : Type u} {Target : Type v}
variable [NormedAddCommGroup Source] [NormedSpace ℝ Source]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target]

/-- A target critical point pulls back to a genuine critical point. -/
theorem pulledBackAction_fderiv_eq_zero_at_target_critical
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (x : Source)
    (hTarget : DifferentiableAt ℝ targetAction (compatibleMap x))
    (hMap : DifferentiableAt ℝ compatibleMap x)
    (hCritical : fderiv ℝ targetAction (compatibleMap x) = 0) :
    fderiv ℝ (pulledBackAction targetAction compatibleMap) x = 0 := by
  have hPullback := pulledBackAction_hasFDerivAt targetAction compatibleMap x
    (fderiv ℝ targetAction (compatibleMap x))
    (fderiv ℝ compatibleMap x)
    hTarget.hasFDerivAt hMap.hasFDerivAt
  simpa [hCritical] using hPullback.fderiv

/-- At a target critical point, the genuine pullback Hessian annihilates any
direction in the kernel of the actual Jacobian, in either argument.  This is
an abstract Fréchet statement and makes no Janus PDE claim. -/
theorem pulledBackAction_second_fderiv_annihilates_jacobian_kernel
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
    (kernelDirection direction : Source)
    (hKernel : (fderiv ℝ compatibleMap x) kernelDirection = 0) :
    fderiv ℝ
        (fun y => fderiv ℝ
          (pulledBackAction targetAction compatibleMap) y) x
          kernelDirection direction = 0 ∧
      fderiv ℝ
        (fun y => fderiv ℝ
          (pulledBackAction targetAction compatibleMap) y) x
          direction kernelDirection = 0 := by
  have hHessian := pulledBackAction_second_fderiv_at_critical
    targetAction compatibleMap hTarget hMap x secondJet targetHessian
    hSecondJet hTargetHessian hCritical
  constructor
  · rw [hHessian]
    simp [hKernel]
  · rw [hHessian]
    rw [jacobianPullbackHessian_symmetric_at_critical
      targetAction compatibleMap hTarget hMap x secondJet targetHessian
      hSecondJet hTargetHessian hCritical direction kernelDirection]
    simp [hKernel]

/-- A continuous linear gauge generator whose image is killed by the actual
Jacobian supplies genuine pullback-Hessian zero modes. -/
theorem pulledBackAction_second_fderiv_annihilates_generated_gauge
    {Gauge : Type w}
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge]
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
    (gaugeGenerator : Gauge →L[ℝ] Source)
    (hGeneratedKernel :
      (fderiv ℝ compatibleMap x).comp gaugeGenerator = 0)
    (parameter : Gauge)
    (direction : Source) :
    fderiv ℝ
        (fun y => fderiv ℝ
          (pulledBackAction targetAction compatibleMap) y) x
          (gaugeGenerator parameter) direction = 0 ∧
      fderiv ℝ
        (fun y => fderiv ℝ
          (pulledBackAction targetAction compatibleMap) y) x
          direction (gaugeGenerator parameter) = 0 := by
  have hKernel :
      (fderiv ℝ compatibleMap x) (gaugeGenerator parameter) = 0 := by
    calc
      (fderiv ℝ compatibleMap x) (gaugeGenerator parameter) =
          ((fderiv ℝ compatibleMap x).comp gaugeGenerator) parameter := rfl
      _ = 0 := by rw [hGeneratedKernel]; rfl
  exact pulledBackAction_second_fderiv_annihilates_jacobian_kernel
    targetAction compatibleMap hTarget hMap x secondJet targetHessian
    hSecondJet hTargetHessian hCritical (gaugeGenerator parameter) direction
    hKernel

end

end P0EFTJanusFrechetPullbackGaugeDegeneracy
end JanusFormal
