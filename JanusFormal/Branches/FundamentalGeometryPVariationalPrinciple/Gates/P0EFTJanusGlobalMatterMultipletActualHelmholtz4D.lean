import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

/-!
# Actual Helmholtz condition for the eight-component matter block

The Euler linearizations below are genuine derivatives of the same unchanged
global matter action.  This gate adds no metric, Maxwell, ghost, boundary or
full Candidate-A sector.
-/

namespace JanusFormal
namespace P0EFTJanusGlobalMatterMultipletActualHelmholtz4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Nonlinear Helmholtz condition for the actual eight-component matter Euler
functional, at every matter background. -/
def GlobalMatterMultipletActualHelmholtzCondition : Prop :=
  ∀ (data : MatterMultipletActionData period hPeriod)
    (fields first second : MatterComponentFamily period hPeriod),
    deriv (fun epsilon : Real =>
      globalMatterMultipletEuler period hPeriod data
        (matterMultipletAffineCurve period hPeriod fields first epsilon) second) 0 =
    deriv (fun epsilon : Real =>
      globalMatterMultipletEuler period hPeriod data
        (matterMultipletAffineCurve period hPeriod fields second epsilon) first) 0

/-- Both derivatives are the mixed Hessians of the same eight-component
matter action, hence commute. -/
theorem global_matter_multiplet_actual_helmholtz_condition :
    GlobalMatterMultipletActualHelmholtzCondition period hPeriod := by
  intro data fields first second
  rw [(globalMatterMultipletEuler_hasDerivAt period hPeriod data fields first
      second).deriv,
    (globalMatterMultipletEuler_hasDerivAt period hPeriod data fields second
      first).deriv]
  exact globalMatterMultipletHessian_symmetric period hPeriod data first second

end

end P0EFTJanusGlobalMatterMultipletActualHelmholtz4D
end JanusFormal
