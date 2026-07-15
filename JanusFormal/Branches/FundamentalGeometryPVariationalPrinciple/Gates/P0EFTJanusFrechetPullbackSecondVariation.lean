import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace JanusFormal
namespace P0EFTJanusFrechetPullbackSecondVariation

set_option autoImplicit false

noncomputable section

universe u v

variable {Source : Type u} {Target : Type v}
variable [NormedAddCommGroup Source] [NormedSpace ℝ Source]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target]

/-- Actual second derivative of a source-to-target map, in curried continuous
linear form. -/
abbrev SourceSecondJet :=
  Source →L[ℝ] Source →L[ℝ] Target

/-- Actual target Hessian, in curried continuous linear form. -/
abbrev TargetHessian :=
  Target →L[ℝ] Target →L[ℝ] ℝ

/-- The nonlinear pullback of a scalar target action. -/
def pulledBackAction
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target) : Source → ℝ :=
  fun x => targetAction (compatibleMap x)

/-- The genuine first-derivative expression supplied by the Fréchet chain
rule. -/
noncomputable def pulledBackGradient
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (x : Source) : Source →L[ℝ] ℝ :=
  (fderiv ℝ targetAction (compatibleMap x)).comp
    (fderiv ℝ compatibleMap x)

/-- The `Jᵀ H J` contribution obtained by pulling the target Hessian back
through the actual Jacobian. -/
def jacobianPullbackHessian
    (jacobian : Source →L[ℝ] Target)
    (targetHessian : TargetHessian (Target := Target)) :
    Source →L[ℝ] Source →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ Source Target ℝ).flip jacobian).comp
    (targetHessian.comp jacobian)

@[simp]
theorem jacobianPullbackHessian_apply_apply
    (jacobian : Source →L[ℝ] Target)
    (targetHessian : TargetHessian (Target := Target))
    (first second : Source) :
    jacobianPullbackHessian jacobian targetHessian first second =
      targetHessian (jacobian first) (jacobian second) := rfl

/-- The off-critical correction obtained by contracting the target gradient
with the actual second jet of the nonlinear map. -/
def gradientSecondJetCorrection
    (targetGradient : Target →L[ℝ] ℝ)
    (secondJet : SourceSecondJet (Source := Source) (Target := Target)) :
    Source →L[ℝ] Source →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ Source Target ℝ targetGradient).comp
    secondJet

@[simp]
theorem gradientSecondJetCorrection_apply_apply
    (targetGradient : Target →L[ℝ] ℝ)
    (secondJet : SourceSecondJet (Source := Source) (Target := Target))
    (first second : Source) :
    gradientSecondJetCorrection targetGradient secondJet first second =
      targetGradient (secondJet first second) := rfl

/-- Complete source second variation: the Jacobian pullback of the target
Hessian plus the gradient--second-jet correction. -/
def sourceSecondVariation
    (jacobian : Source →L[ℝ] Target)
    (targetGradient : Target →L[ℝ] ℝ)
    (targetHessian : TargetHessian (Target := Target))
    (secondJet : SourceSecondJet (Source := Source) (Target := Target)) :
    Source →L[ℝ] Source →L[ℝ] ℝ :=
  jacobianPullbackHessian jacobian targetHessian +
    gradientSecondJetCorrection targetGradient secondJet

@[simp]
theorem sourceSecondVariation_apply_apply
    (jacobian : Source →L[ℝ] Target)
    (targetGradient : Target →L[ℝ] ℝ)
    (targetHessian : TargetHessian (Target := Target))
    (secondJet : SourceSecondJet (Source := Source) (Target := Target))
    (first second : Source) :
    sourceSecondVariation jacobian targetGradient targetHessian secondJet
        first second =
      targetHessian (jacobian first) (jacobian second) +
        targetGradient (secondJet first second) := rfl

/-- First-order Fréchet chain rule for the nonlinear pullback. -/
theorem pulledBackAction_hasFDerivAt
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (x : Source)
    (targetGradient : Target →L[ℝ] ℝ)
    (jacobian : Source →L[ℝ] Target)
    (hTarget : HasFDerivAt targetAction targetGradient (compatibleMap x))
    (hMap : HasFDerivAt compatibleMap jacobian x) :
    HasFDerivAt (pulledBackAction targetAction compatibleMap)
      (targetGradient.comp jacobian) x := by
  change HasFDerivAt (targetAction ∘ compatibleMap)
    (targetGradient.comp jacobian) x
  exact hTarget.comp x hMap

/-- At every point where both maps are differentiable, the actual derivative
of the pullback is the displayed composed gradient. -/
theorem pulledBackAction_fderiv
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (hTarget : Differentiable ℝ targetAction)
    (hMap : Differentiable ℝ compatibleMap)
    (x : Source) :
    fderiv ℝ (pulledBackAction targetAction compatibleMap) x =
      pulledBackGradient targetAction compatibleMap x := by
  exact (pulledBackAction_hasFDerivAt targetAction compatibleMap x
    (fderiv ℝ targetAction (compatibleMap x))
    (fderiv ℝ compatibleMap x)
    (hTarget (compatibleMap x)).hasFDerivAt
    (hMap x).hasFDerivAt).fderiv

/-- Differentiating the genuine pullback-gradient expression gives exactly
`Jᵀ H J` plus the target-gradient contraction with the map's second jet. -/
theorem pulledBackGradient_hasFDerivAt
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (x : Source)
    (jacobian : Source →L[ℝ] Target)
    (secondJet : SourceSecondJet (Source := Source) (Target := Target))
    (targetHessian : TargetHessian (Target := Target))
    (hMap : HasFDerivAt compatibleMap jacobian x)
    (hSecondJet :
      HasFDerivAt (fun y => fderiv ℝ compatibleMap y) secondJet x)
    (hTargetHessian :
      HasFDerivAt (fun z => fderiv ℝ targetAction z)
        targetHessian (compatibleMap x)) :
    HasFDerivAt (pulledBackGradient targetAction compatibleMap)
      (sourceSecondVariation jacobian
        (fderiv ℝ targetAction (compatibleMap x))
        targetHessian secondJet) x := by
  have hTargetAlong :
      HasFDerivAt
        (fun y => fderiv ℝ targetAction (compatibleMap y))
        (targetHessian.comp jacobian) x :=
    hTargetHessian.comp x hMap
  have hComposition := hTargetAlong.clm_comp hSecondJet
  change HasFDerivAt
    (fun y => (fderiv ℝ targetAction (compatibleMap y)).comp
      (fderiv ℝ compatibleMap y))
    (sourceSecondVariation jacobian
      (fderiv ℝ targetAction (compatibleMap x))
      targetHessian secondJet) x
  simpa [sourceSecondVariation, jacobianPullbackHessian,
    gradientSecondJetCorrection, hMap.fderiv, add_comm] using hComposition

/-- The actual derivative of the actual pullback derivative is the complete
second-variation formula.  Global differentiability is used only to identify
the chain-rule gradient with `fderiv` in a neighborhood of the base point. -/
theorem pulledBackAction_fderiv_hasFDerivAt
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
        targetHessian (compatibleMap x)) :
    HasFDerivAt
      (fun y => fderiv ℝ (pulledBackAction targetAction compatibleMap) y)
      (sourceSecondVariation (fderiv ℝ compatibleMap x)
        (fderiv ℝ targetAction (compatibleMap x))
        targetHessian secondJet) x := by
  have hFunction :
      (fun y => fderiv ℝ (pulledBackAction targetAction compatibleMap) y) =
        pulledBackGradient targetAction compatibleMap := by
    funext y
    exact pulledBackAction_fderiv targetAction compatibleMap
      hTarget hMap y
  rw [hFunction]
  exact pulledBackGradient_hasFDerivAt targetAction compatibleMap x
    (fderiv ℝ compatibleMap x) secondJet targetHessian
    (hMap x).hasFDerivAt hSecondJet hTargetHessian

/-- Computed actual second Fréchet derivative of the nonlinear pullback. -/
theorem pulledBackAction_second_fderiv
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
        targetHessian (compatibleMap x)) :
    fderiv ℝ
        (fun y => fderiv ℝ
          (pulledBackAction targetAction compatibleMap) y) x =
      sourceSecondVariation (fderiv ℝ compatibleMap x)
        (fderiv ℝ targetAction (compatibleMap x))
        targetHessian secondJet :=
  (pulledBackAction_fderiv_hasFDerivAt targetAction compatibleMap
    hTarget hMap x secondJet targetHessian
    hSecondJet hTargetHessian).fderiv

/-- Pointwise form of the true nonlinear second-variation chain rule. -/
theorem pulledBackAction_second_fderiv_apply
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
    fderiv ℝ
        (fun y => fderiv ℝ
          (pulledBackAction targetAction compatibleMap) y) x first second =
      targetHessian
          ((fderiv ℝ compatibleMap x) first)
          ((fderiv ℝ compatibleMap x) second) +
        (fderiv ℝ targetAction (compatibleMap x))
          (secondJet first second) := by
  rw [pulledBackAction_second_fderiv targetAction compatibleMap
    hTarget hMap x secondJet targetHessian hSecondJet hTargetHessian]
  exact sourceSecondVariation_apply_apply
    (fderiv ℝ compatibleMap x)
    (fderiv ℝ targetAction (compatibleMap x))
    targetHessian secondJet first second

/-- At a target critical point the gradient--second-jet correction vanishes,
leaving exactly `Jᵀ H J`. -/
theorem sourceSecondVariation_eq_jacobianPullback_of_gradient_eq_zero
    (jacobian : Source →L[ℝ] Target)
    (targetGradient : Target →L[ℝ] ℝ)
    (targetHessian : TargetHessian (Target := Target))
    (secondJet : SourceSecondJet (Source := Source) (Target := Target))
    (hCritical : targetGradient = 0) :
    sourceSecondVariation jacobian targetGradient targetHessian secondJet =
      jacobianPullbackHessian jacobian targetHessian := by
  ext first second
  simp [sourceSecondVariation_apply_apply, hCritical]

/-- Critical-point reduction of the genuine second Fréchet derivative of
the pullback action. -/
theorem pulledBackAction_second_fderiv_at_critical
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
    (hCritical : fderiv ℝ targetAction (compatibleMap x) = 0) :
    fderiv ℝ
        (fun y => fderiv ℝ
          (pulledBackAction targetAction compatibleMap) y) x =
      jacobianPullbackHessian (fderiv ℝ compatibleMap x)
        targetHessian := by
  rw [pulledBackAction_second_fderiv targetAction compatibleMap
    hTarget hMap x secondJet targetHessian hSecondJet hTargetHessian]
  exact sourceSecondVariation_eq_jacobianPullback_of_gradient_eq_zero
    (fderiv ℝ compatibleMap x)
    (fderiv ℝ targetAction (compatibleMap x))
    targetHessian secondJet hCritical

end

end P0EFTJanusFrechetPullbackSecondVariation
end JanusFormal
