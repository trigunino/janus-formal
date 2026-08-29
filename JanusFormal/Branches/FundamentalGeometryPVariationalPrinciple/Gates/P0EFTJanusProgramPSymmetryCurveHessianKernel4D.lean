import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Hessian zero modes from general symmetry curves

Gauge and diffeomorphism orbits are not generally affine translations in a
configuration chart.  The intrinsic Noether argument only needs a differentiable
curve `γ` through the base point, its tangent vector, and local invariance of
the action gradient along that curve.

Differentiating

`∇S (γ(t)) = ∇S (γ(0))`

at `t = 0` gives

`D(∇S)_{γ(0)} (γ'(0)) = 0`.

This file records that general form.  The affine-orbit gate is a special case.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSymmetryCurveHessianKernel4D

set_option autoImplicit false
noncomputable section

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

local instance continuousLinearMapNormedAddCommGroup :
    NormedAddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance continuousLinearMapNormedSpace :
    NormedSpace Real (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

/-- Differentiable one-parameter curve through `point`, with the ambient vector
`generator` as its derivative at zero. -/
structure SymmetryCurveAt (point generator : E) where
  curve : Real → E
  derivative : Real →L[Real] E
  curve_zero : curve 0 = point
  hasFDerivAt_zero : HasFDerivAt curve derivative 0
  derivative_one : derivative 1 = generator

/-- A map is locally constant along the selected symmetry curve. -/
def CurveEventuallyInvariantAt
    (map : E → F) {point generator : E}
    (orbit : SymmetryCurveAt point generator) : Prop :=
  (fun parameter : Real => map (orbit.curve parameter)) =ᶠ[𝓝 0]
    fun _ : Real => map point

/-- General curve version of the infinitesimal Noether identity. -/
theorem fderiv_apply_eq_zero_of_curveEventuallyInvariant
    (map : E → F) (point generator : E)
    (orbit : SymmetryCurveAt point generator)
    (hDifferentiable : DifferentiableAt Real map point)
    (hInvariant : CurveEventuallyInvariantAt map orbit) :
    fderiv Real map point generator = 0 := by
  have hMapAtCurve : DifferentiableAt Real map (orbit.curve 0) := by
    simpa [orbit.curve_zero] using hDifferentiable
  have hChain :
      fderiv Real (fun parameter : Real => map (orbit.curve parameter)) 0 =
        (fderiv Real map point).comp orbit.derivative := by
    have hRaw := fderiv_comp (𝕜 := Real) (x := (0 : Real))
      hMapAtCurve orbit.hasFDerivAt_zero.differentiableAt
    rw [orbit.hasFDerivAt_zero.fderiv] at hRaw
    simpa [Function.comp_def, orbit.curve_zero] using hRaw
  have hCurveDerivativeZero :
      fderiv Real (fun parameter : Real => map (orbit.curve parameter)) 0 = 0 := by
    calc
      fderiv Real (fun parameter : Real => map (orbit.curve parameter)) 0 =
          fderiv Real (fun _ : Real => map point) 0 :=
        Filter.EventuallyEq.fderiv_eq hInvariant
      _ = 0 := fderiv_const_apply (𝕜 := Real) (x := (0 : Real)) (map point)
  have hCompositeZero :
      (fderiv Real map point).comp orbit.derivative = 0 := by
    rw [← hChain]
    exact hCurveDerivativeZero
  have hAtOne := congrArg
    (fun derivative : Real →L[Real] F => derivative 1) hCompositeZero
  simpa [ContinuousLinearMap.comp_apply, orbit.derivative_one] using hAtOne

/-- Gradient invariance of an action along a genuine symmetry curve. -/
def ActionGradientCurveEventuallyInvariantAt
    (action : E → Real) {point generator : E}
    (orbit : SymmetryCurveAt point generator) : Prop :=
  CurveEventuallyInvariantAt
    (fun state => fderiv Real action state) orbit

/-- General-curve second-Fréchet kernel theorem. -/
theorem secondFrechet_apply_eq_zero_of_gradientCurveInvariant
    (action : E → Real) (point generator : E)
    (orbit : SymmetryCurveAt point generator)
    (hGradientDifferentiable : DifferentiableAt Real
      (fun state => fderiv Real action state) point)
    (hInvariant : ActionGradientCurveEventuallyInvariantAt action orbit) :
    fderiv Real (fun state => fderiv Real action state) point generator = 0 :=
  fderiv_apply_eq_zero_of_curveEventuallyInvariant
    (fun state => fderiv Real action state) point generator orbit
      hGradientDifferentiable hInvariant

/-- Public general symmetry-curve checkpoint. -/
theorem symmetry_curve_hessian_kernel_gate
    (action : E → Real) (point generator : E)
    (orbit : SymmetryCurveAt point generator)
    (hGradientDifferentiable : DifferentiableAt Real
      (fun state => fderiv Real action state) point)
    (hInvariant : ActionGradientCurveEventuallyInvariantAt action orbit) :
    fderiv Real (fun state => fderiv Real action state) point generator = 0 :=
  secondFrechet_apply_eq_zero_of_gradientCurveInvariant action point generator
    orbit hGradientDifferentiable hInvariant

end
end P0EFTJanusProgramPSymmetryCurveHessianKernel4D
end JanusFormal
