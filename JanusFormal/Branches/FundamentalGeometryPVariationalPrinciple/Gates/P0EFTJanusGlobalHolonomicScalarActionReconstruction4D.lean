import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D

namespace JanusFormal
namespace P0EFTJanusGlobalHolonomicScalarActionReconstruction4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The unchanged global scalar action is reconstructed, with its exact
quadratic normalization, from the diagonal of its genuine mixed Hessian. -/
theorem globalHolonomicScalarAction_eq_half_actualMixedHessian
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field base : GlobalScalarTestSpace period hPeriod) :
    globalHolonomicScalarAction period hPeriod data.massSquared data.magnitude
        field data.measure =
      (1 / 2 : Real) *
        globalHolonomicScalarActionMixedHessian period hPeriod data base
          field field := by
  rw [globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod data
    base field field, weakGlobalHolonomicScalarJacobiOperator_apply]
  unfold globalHolonomicScalarAction globalHolonomicScalarJacobiForm
  rw [show globalHolonomicScalarDensity period hPeriod data.massSquared
      data.magnitude field =
      fun point => (1 / 2 : Real) *
        globalHolonomicScalarJacobiDensity period hPeriod data.massSquared
          data.magnitude field field point from by
    funext point
    exact globalHolonomicScalarDensity_eq_half_jacobi period hPeriod
      data.massSquared data.magnitude field point]
  rw [integral_const_mul]

end

end P0EFTJanusGlobalHolonomicScalarActionReconstruction4D
end JanusFormal
