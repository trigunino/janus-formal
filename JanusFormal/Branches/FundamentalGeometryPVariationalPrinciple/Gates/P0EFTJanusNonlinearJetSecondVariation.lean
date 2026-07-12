import Mathlib

namespace JanusFormal
namespace P0EFTJanusNonlinearJetSecondVariation

set_option autoImplicit false

/-- Quadratic target action near one target coordinate. -/
@[ext] structure QuadraticTargetAction where
  valueAtOrigin : ℝ
  gradientAtOrigin : ℝ
  hessianAtOrigin : ℝ

/-- Quadratic compatible-jet map near one source coordinate. -/
@[ext] structure QuadraticJetMap where
  linearPart : ℝ
  secondPart : ℝ

/-- Target action value. -/
noncomputable def targetActionValue
    (action : QuadraticTargetAction)
    (target : ℝ) : ℝ :=
  action.valueAtOrigin +
    action.gradientAtOrigin * target +
    action.hessianAtOrigin * target ^ 2 / 2

/-- Nonlinear compatible-jet map. -/
noncomputable def jetMapValue
    (jetMap : QuadraticJetMap)
    (source : ℝ) : ℝ :=
  jetMap.linearPart * source +
    jetMap.secondPart * source ^ 2 / 2

/-- Pullback action. -/
noncomputable def pulledBackActionValue
    (action : QuadraticTargetAction)
    (jetMap : QuadraticJetMap)
    (source : ℝ) : ℝ :=
  targetActionValue action (jetMapValue jetMap source)

/-- Formal gradient coefficient of the pullback at the origin. -/
def pulledBackGradientAtOrigin
    (action : QuadraticTargetAction)
    (jetMap : QuadraticJetMap) : ℝ :=
  action.gradientAtOrigin * jetMap.linearPart

/--
Formal Hessian coefficient of the nonlinear pullback.  It contains the usual
`Jᵀ H J` term and a second-variation correction weighted by the target gradient.
-/
def pulledBackHessianAtOrigin
    (action : QuadraticTargetAction)
    (jetMap : QuadraticJetMap) : ℝ :=
  action.hessianAtOrigin * jetMap.linearPart ^ 2 +
    action.gradientAtOrigin * jetMap.secondPart

/-- Cubic coefficient in the exact pullback expansion. -/
def pulledBackCubicCoefficient
    (action : QuadraticTargetAction)
    (jetMap : QuadraticJetMap) : ℝ :=
  action.hessianAtOrigin *
    jetMap.linearPart * jetMap.secondPart / 2

/-- Quartic coefficient in the exact pullback expansion. -/
def pulledBackQuarticCoefficient
    (action : QuadraticTargetAction)
    (jetMap : QuadraticJetMap) : ℝ :=
  action.hessianAtOrigin * jetMap.secondPart ^ 2 / 8

/-- Exact polynomial chain-rule expansion through quartic order. -/
theorem nonlinear_pullback_exact_expansion
    (action : QuadraticTargetAction)
    (jetMap : QuadraticJetMap)
    (source : ℝ) :
    pulledBackActionValue action jetMap source =
      action.valueAtOrigin +
      pulledBackGradientAtOrigin action jetMap * source +
      pulledBackHessianAtOrigin action jetMap * source ^ 2 / 2 +
      pulledBackCubicCoefficient action jetMap * source ^ 3 +
      pulledBackQuarticCoefficient action jetMap * source ^ 4 := by
  unfold pulledBackActionValue targetActionValue jetMapValue
    pulledBackGradientAtOrigin pulledBackHessianAtOrigin
    pulledBackCubicCoefficient pulledBackQuarticCoefficient
  ring

/-- At a target critical point, the nonlinear correction disappears. -/
theorem critical_target_reduces_to_jacobian_pullback
    (action : QuadraticTargetAction)
    (jetMap : QuadraticJetMap)
    (hCritical : action.gradientAtOrigin = 0) :
    pulledBackHessianAtOrigin action jetMap =
      action.hessianAtOrigin * jetMap.linearPart ^ 2 := by
  unfold pulledBackHessianAtOrigin
  rw [hCritical]
  ring

/-- Away from a target critical point, the second jet changes the source Hessian. -/
def noncriticalAction : QuadraticTargetAction :=
  { valueAtOrigin := 0
    gradientAtOrigin := 1
    hessianAtOrigin := 1 }

/-- Linear compatible-jet map. -/
def linearJetMap : QuadraticJetMap :=
  { linearPart := 1
    secondPart := 0 }

/-- Nonlinear compatible-jet map with the same linearization. -/
def curvedJetMap : QuadraticJetMap :=
  { linearPart := 1
    secondPart := 1 }

/-- Same Jacobian and target Hessian can give different source Hessians off shell. -/
theorem same_jacobian_different_second_jet_changes_hessian :
    linearJetMap.linearPart = curvedJetMap.linearPart /\
    pulledBackHessianAtOrigin noncriticalAction linearJetMap ≠
      pulledBackHessianAtOrigin noncriticalAction curvedJetMap := by
  constructor
  · rfl
  · norm_num [pulledBackHessianAtOrigin,
      noncriticalAction, linearJetMap, curvedJetMap]

/-- Critical target action used to show second-jet independence on shell. -/
def criticalAction : QuadraticTargetAction :=
  { valueAtOrigin := 0
    gradientAtOrigin := 0
    hessianAtOrigin := 1 }

/-- At a critical point, equal Jacobians give equal pulled-back Hessians. -/
theorem critical_point_removes_second_jet_dependence :
    pulledBackHessianAtOrigin criticalAction linearJetMap =
      pulledBackHessianAtOrigin criticalAction curvedJetMap := by
  norm_num [pulledBackHessianAtOrigin,
    criticalAction, linearJetMap, curvedJetMap]

/--
Correct nonlinear chain-rule status.  The formula `Jᵀ H J` is exact for the
second variation of a pulled-back action at a target critical point.  Away from
criticality, the target gradient contracts with the second derivative of the
geometric/jet map and cannot be omitted.
-/
structure NonlinearPullbackPhysicalStatus where
  nonlinearCompatibleJetMapConstructed : Prop
  targetActionConstructed : Prop
  targetCriticalPointProved : Prop
  firstVariationChainRuleProved : Prop
  secondVariationChainRuleProved : Prop
  secondJetCorrectionIdentified : Prop
  correctionVanishingAtCriticalPointProved : Prop
  pulledBackFredholmHessianDerived : Prop


def nonlinearPullbackPhysicalClosure
    (s : NonlinearPullbackPhysicalStatus) : Prop :=
  s.nonlinearCompatibleJetMapConstructed /\
  s.targetActionConstructed /\
  s.targetCriticalPointProved /\
  s.firstVariationChainRuleProved /\
  s.secondVariationChainRuleProved /\
  s.secondJetCorrectionIdentified /\
  s.correctionVanishingAtCriticalPointProved /\
  s.pulledBackFredholmHessianDerived

end P0EFTJanusNonlinearJetSecondVariation
end JanusFormal
