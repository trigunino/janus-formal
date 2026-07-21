import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The actual directional derivative of the existing global D8 scalar action. -/
def globalHolonomicScalarActionDirectionalDerivative
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field variation : GlobalScalarTestSpace period hPeriod) : Real :=
  deriv (fun epsilon : Real =>
    globalHolonomicScalarAction period hPeriod data.massSquared data.magnitude
      (scalarAffineCurve period hPeriod field variation epsilon) data.measure) 0

/-- The actual derivative is the previously constructed weak Euler pairing. -/
theorem globalHolonomicScalarActionDirectionalDerivative_eq_weakEuler
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field variation : GlobalScalarTestSpace period hPeriod) :
    globalHolonomicScalarActionDirectionalDerivative period hPeriod data field variation =
      weakGlobalHolonomicScalarEulerOperator period hPeriod data field variation := by
  exact (globalHolonomicScalarAction_hasDerivAt_weakEuler period hPeriod data
    field variation).deriv

/-- The Jacobi pairing is the genuine mixed second variation of that same
global action, obtained by differentiating its actual directional derivative
along a second affine field direction. -/
theorem globalHolonomicScalarActionDirectionalDerivative_hasDerivAt
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field first second : GlobalScalarTestSpace period hPeriod) :
    HasDerivAt
      (fun epsilon : Real =>
        globalHolonomicScalarActionDirectionalDerivative period hPeriod data
          (scalarAffineCurve period hPeriod field first epsilon) second)
      (weakGlobalHolonomicScalarJacobiOperator period hPeriod data first second) 0 := by
  rw [show (fun epsilon : Real =>
      globalHolonomicScalarActionDirectionalDerivative period hPeriod data
        (scalarAffineCurve period hPeriod field first epsilon) second) =
      (fun epsilon : Real =>
        weakGlobalHolonomicScalarEulerOperator period hPeriod data
          (scalarAffineCurve period hPeriod field first epsilon) second) from by
    funext epsilon
    exact globalHolonomicScalarActionDirectionalDerivative_eq_weakEuler
      period hPeriod data
      (scalarAffineCurve period hPeriod field first epsilon) second]
  exact weakGlobalHolonomicScalarEulerOperator_hasDerivAt period hPeriod data
    field first second

/-- The actual mixed Hessian obtained from the preceding derivative. -/
def globalHolonomicScalarActionMixedHessian
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field first second : GlobalScalarTestSpace period hPeriod) : Real :=
  deriv (fun epsilon : Real =>
    globalHolonomicScalarActionDirectionalDerivative period hPeriod data
      (scalarAffineCurve period hPeriod field first epsilon) second) 0

theorem globalHolonomicScalarActionMixedHessian_eq_jacobi
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field first second : GlobalScalarTestSpace period hPeriod) :
    globalHolonomicScalarActionMixedHessian period hPeriod data field first second =
      weakGlobalHolonomicScalarJacobiOperator period hPeriod data first second := by
  exact (globalHolonomicScalarActionDirectionalDerivative_hasDerivAt period
    hPeriod data field first second).deriv

/-- Schwarz symmetry for the actual mixed Hessian of the global D8 action. -/
theorem globalHolonomicScalarActionMixedHessian_symmetric
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field first second : GlobalScalarTestSpace period hPeriod) :
    globalHolonomicScalarActionMixedHessian period hPeriod data field first second =
      globalHolonomicScalarActionMixedHessian period hPeriod data field second first := by
  rw [globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod data
      field first second,
    globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod data
      field second first]
  exact weakGlobalHolonomicScalarJacobiOperator_symmetric period hPeriod data
    first second

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D
end JanusFormal
