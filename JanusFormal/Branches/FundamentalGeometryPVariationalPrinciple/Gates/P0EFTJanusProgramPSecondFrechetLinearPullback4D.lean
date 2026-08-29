import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

/-!
# Second Fréchet derivative under a bounded linear pullback

If `f : F → ℝ` is `C²` at `L x`, then the Hessian of `f ∘ L` at `x` is the
bilinear pullback of the Hessian of `f` by the continuous linear map `L`.

This is the generic calculus step needed to consume the H10 action equality at
the Hessian level.  In particular, a local Robin block identified with the
completed GHY action after one bounded linear projection has no independent
Hessian datum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSecondFrechetLinearPullback4D

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Filter Topology
open P0EFTJanusConvexHelmholtzReconstruction

universe u v

/-- First derivative of a scalar action after a bounded linear pullback. -/
theorem actionGradient_linearPullback
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (action : F → Real)
    (projection : E →L[Real] F)
    (point : E)
    (hAction : DifferentiableAt Real action (projection point)) :
    actionGradient (fun state => action (projection state)) point =
      (actionGradient action (projection point)).comp projection := by
  unfold actionGradient
  rw [fderiv_fun_comp point hAction projection.differentiableAt]
  simp

/-- Hessian chain rule for a bounded linear projection. -/
theorem secondFrechet_linearPullback
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (action : F → Real)
    (projection : E →L[Real] F)
    (base : E)
    (hC2 : ContDiffAt Real 2 action (projection base)) :
    fderiv Real
        (actionGradient (fun state => action (projection state))) base =
      (fderiv Real (actionGradient action) (projection base)).bilinearComp
        projection projection := by
  have hGradient :
      DifferentiableAt Real (actionGradient action) (projection base) :=
    (hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFirst :
      actionGradient (fun state => action (projection state)) =ᶠ[𝓝 base]
        fun state => (actionGradient action (projection state)).comp projection := by
    have hEventuallyC2 := hC2.eventually (by norm_num)
    have hPulledBack :
        ∀ᶠ state : E in 𝓝 base, ContDiffAt Real 2 action (projection state) :=
      projection.continuous.continuousAt hEventuallyC2
    filter_upwards [hPulledBack] with state hState
    exact actionGradient_linearPullback action projection state
      (hState.differentiableAt (by norm_num))
  rw [hFirst.fderiv_eq]
  let gradientAlong : E → F →L[Real] Real :=
    fun state => actionGradient action (projection state)
  have hGradientAlong : DifferentiableAt Real gradientAlong base := by
    exact hGradient.comp base projection.differentiableAt
  have hProjectionConstant :
      DifferentiableAt Real (fun _ : E => projection) base :=
    differentiableAt_const projection
  rw [fderiv_clm_comp hGradientAlong hProjectionConstant]
  have hGradientAlongDerivative :
      fderiv Real gradientAlong base =
        fderiv Real (actionGradient action) (projection base) ∘SL projection := by
    simpa using fderiv_fun_comp base hGradient projection.differentiableAt
  rw [hGradientAlongDerivative]
  have hProjectionDerivative :
      fderiv Real (fun _ : E => projection) base = 0 :=
    (hasFDerivAt_const (x := base) projection).fderiv
  rw [hProjectionDerivative]
  simp only [ContinuousLinearMap.comp_zero, zero_add]
  ext first second
  rfl

/-- Equality of scalar actions transports the linear-pullback Hessian formula. -/
theorem secondFrechet_eq_bilinearComp_of_action_eq
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (localAction : E → Real)
    (completedAction : F → Real)
    (projection : E →L[Real] F)
    (base : E)
    (hActionEq : localAction = fun state => completedAction (projection state))
    (hC2 : ContDiffAt Real 2 completedAction (projection base)) :
    fderiv Real (actionGradient localAction) base =
      (fderiv Real (actionGradient completedAction) (projection base)).bilinearComp
        projection projection := by
  rw [hActionEq]
  exact secondFrechet_linearPullback completedAction projection base hC2

/-- Public calculus checkpoint. -/
theorem second_frechet_linear_pullback_gate
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (action : F → Real)
    (projection : E →L[Real] F)
    (base : E)
    (hC2 : ContDiffAt Real 2 action (projection base)) :
    fderiv Real
        (actionGradient (fun state => action (projection state))) base =
      (fderiv Real (actionGradient action) (projection base)).bilinearComp
        projection projection :=
  secondFrechet_linearPullback action projection base hC2

end
end P0EFTJanusProgramPSecondFrechetLinearPullback4D
end JanusFormal
