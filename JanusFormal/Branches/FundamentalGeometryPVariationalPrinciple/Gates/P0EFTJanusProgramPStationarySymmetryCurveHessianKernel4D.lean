import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSymmetryCurveHessianKernel4D

/-!
# Tangents to stationary symmetry families are Hessian zero modes

For a symmetry orbit through a stationary background, every nearby point of
the orbit is stationary.  The action gradient is therefore identically zero
along the orbit, and its derivative in the orbit tangent vanishes.

This is the Jacobi-field form of the Noether argument: a differentiable family
of solutions produces a vector in the kernel of the linearized equations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPStationarySymmetryCurveHessianKernel4D

set_option autoImplicit false
noncomputable section

open Filter Topology
open P0EFTJanusProgramPSymmetryCurveHessianKernel4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- The action is stationary at every sufficiently small point of the selected
curve. -/
def ActionStationaryAlongCurveEventually
    (action : E → Real) {point generator : E}
    (orbit : SymmetryCurveAt point generator) : Prop :=
  ∀ᶠ parameter : Real in 𝓝 0,
    fderiv Real action (orbit.curve parameter) = 0

/-- A stationary base point and an eventually stationary curve give gradient
invariance along the curve. -/
theorem gradientCurveInvariant_of_stationaryCurve
    (action : E → Real) (point generator : E)
    (orbit : SymmetryCurveAt point generator)
    (hPointStationary : fderiv Real action point = 0)
    (hCurveStationary : ActionStationaryAlongCurveEventually action orbit) :
    ActionGradientCurveEventuallyInvariantAt action orbit := by
  filter_upwards [hCurveStationary] with parameter hStationary
  rw [hStationary, hPointStationary]

/-- Tangent to a stationary solution family lies in the genuine Hessian
kernel. -/
theorem secondFrechet_apply_eq_zero_of_stationaryCurve
    (action : E → Real) (point generator : E)
    (orbit : SymmetryCurveAt point generator)
    (hGradientDifferentiable : DifferentiableAt Real
      (fun state => fderiv Real action state) point)
    (hPointStationary : fderiv Real action point = 0)
    (hCurveStationary : ActionStationaryAlongCurveEventually action orbit) :
    fderiv Real (fun state => fderiv Real action state) point generator = 0 :=
  secondFrechet_apply_eq_zero_of_gradientCurveInvariant action point generator
    orbit hGradientDifferentiable
      (gradientCurveInvariant_of_stationaryCurve action point generator orbit
        hPointStationary hCurveStationary)

/-- Public stationary-family checkpoint. -/
theorem stationary_symmetry_curve_hessian_kernel_gate
    (action : E → Real) (point generator : E)
    (orbit : SymmetryCurveAt point generator)
    (hGradientDifferentiable : DifferentiableAt Real
      (fun state => fderiv Real action state) point)
    (hPointStationary : fderiv Real action point = 0)
    (hCurveStationary : ActionStationaryAlongCurveEventually action orbit) :
    fderiv Real (fun state => fderiv Real action state) point generator = 0 :=
  secondFrechet_apply_eq_zero_of_stationaryCurve action point generator orbit
    hGradientDifferentiable hPointStationary hCurveStationary

end
end P0EFTJanusProgramPStationarySymmetryCurveHessianKernel4D
end JanusFormal
