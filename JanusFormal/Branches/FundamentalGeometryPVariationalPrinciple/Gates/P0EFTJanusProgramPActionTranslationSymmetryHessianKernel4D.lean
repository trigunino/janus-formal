import Mathlib.Analysis.Calculus.FDeriv.Add
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSymmetryOrbitHessianKernel4D

/-!
# From action invariance to Hessian zero modes

The preceding Noether kernel gate accepts invariance of the action gradient
along an affine orbit.  The physically primitive statement is invariance of
the action itself under the corresponding local translations.

If, for every sufficiently small parameter `t`, the functions

`x ↦ S (x + t • v)` and `x ↦ S x`

agree near the base point, their Fréchet derivatives there agree.  The chain
rule for the affine translation turns this equality into invariance of the
action gradient along `x₀ + t • v`.  The generic symmetry-orbit theorem then
places `v` in the Hessian kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActionTranslationSymmetryHessianKernel4D

set_option autoImplicit false
noncomputable section

open Filter Topology
open P0EFTJanusProgramPSymmetryOrbitHessianKernel4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Local translation invariance of an action around one base point and one
candidate infinitesimal symmetry direction. -/
def ActionTranslationEventuallyInvariantAt
    (action : E → Real) (point vector : E) : Prop :=
  ∀ᶠ parameter : Real in 𝓝 0,
    (fun state : E => action (state + parameter • vector)) =ᶠ[𝓝 point]
      action

/-- Fixed affine translation has derivative equal to the identity. -/
theorem affineTranslation_hasFDerivAt
    (point vector : E) (parameter : Real) :
    HasFDerivAt (fun state : E => state + parameter • vector)
      (ContinuousLinearMap.id Real E) point := by
  simpa using (hasFDerivAt_id point).add_const (parameter • vector)

/-- Local invariance of the action implies local invariance of its gradient
along the generated orbit. -/
theorem gradientOrbitInvariant_of_actionTranslationInvariant
    (action : E → Real) (point vector : E)
    (hActionDifferentiable : Differentiable Real action)
    (hInvariant : ActionTranslationEventuallyInvariantAt action point vector) :
    ActionGradientOrbitEventuallyInvariantAt action point vector := by
  filter_upwards [hInvariant] with parameter hParameter
  have hTranslation := affineTranslation_hasFDerivAt point vector parameter
  have hActionAt : DifferentiableAt Real action
      (point + parameter • vector) :=
    hActionDifferentiable (point + parameter • vector)
  have hChain :
      fderiv Real (fun state : E => action (state + parameter • vector)) point =
        fderiv Real action (point + parameter • vector) := by
    have hComp :=
      (hActionAt.hasFDerivAt.comp point hTranslation).fderiv
    simpa [ContinuousLinearMap.comp_id] using hComp
  calc
    fderiv Real action
        (affineSymmetryOrbit point vector parameter) =
      fderiv Real action (point + parameter • vector) := by
        rfl
    _ = fderiv Real
        (fun state : E => action (state + parameter • vector)) point :=
      hChain.symm
    _ = fderiv Real action point :=
      hParameter.fderiv_eq

/-- Action-level Noether kernel theorem. -/
theorem secondFrechet_apply_eq_zero_of_actionTranslationInvariant
    (action : E → Real) (point vector : E)
    (hActionDifferentiable : Differentiable Real action)
    (hGradientDifferentiable : DifferentiableAt Real
      (fun state => fderiv Real action state) point)
    (hInvariant : ActionTranslationEventuallyInvariantAt action point vector) :
    fderiv Real (fun state => fderiv Real action state) point vector = 0 :=
  secondFrechet_apply_eq_zero_of_gradientOrbitInvariant action point vector
    hGradientDifferentiable
    (gradientOrbitInvariant_of_actionTranslationInvariant action point vector
      hActionDifferentiable hInvariant)

/-- Public action-symmetry checkpoint. -/
theorem action_translation_symmetry_hessian_kernel_gate
    (action : E → Real) (point vector : E)
    (hActionDifferentiable : Differentiable Real action)
    (hGradientDifferentiable : DifferentiableAt Real
      (fun state => fderiv Real action state) point)
    (hInvariant : ActionTranslationEventuallyInvariantAt action point vector) :
    fderiv Real (fun state => fderiv Real action state) point vector = 0 :=
  secondFrechet_apply_eq_zero_of_actionTranslationInvariant action point vector
    hActionDifferentiable hGradientDifferentiable hInvariant

end
end P0EFTJanusProgramPActionTranslationSymmetryHessianKernel4D
end JanusFormal
