import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D

namespace JanusFormal
namespace P0EFTJanusGlobalHolonomicScalarActualHelmholtz4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Nonlinear Helmholtz condition for the actual global D8 scalar Euler
functional, stated at every background field. -/
def GlobalHolonomicScalarActualHelmholtzCondition : Prop :=
  ∀ (data : GlobalHolonomicScalarFormData period hPeriod)
    (field first second : GlobalScalarTestSpace period hPeriod),
    deriv (fun epsilon : Real =>
      globalHolonomicScalarActionDirectionalDerivative period hPeriod data
        (scalarAffineCurve period hPeriod field first epsilon) second) 0 =
    deriv (fun epsilon : Real =>
      globalHolonomicScalarActionDirectionalDerivative period hPeriod data
        (scalarAffineCurve period hPeriod field second epsilon) first) 0

/-- The condition follows from Schwarz symmetry of the genuine mixed second
variation of the same unchanged global scalar action. -/
theorem global_holonomic_scalar_actual_helmholtz_condition :
    GlobalHolonomicScalarActualHelmholtzCondition period hPeriod := by
  intro data field first second
  exact globalHolonomicScalarActionMixedHessian_symmetric period hPeriod data
    field first second

end

end P0EFTJanusGlobalHolonomicScalarActualHelmholtz4D
end JanusFormal
