import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalHolonomicScalarActionReconstruction4D

namespace JanusFormal
namespace P0EFTJanusGlobalMatterMultipletActionReconstruction4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalHolonomicScalarActionReconstruction4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The single eight-component matter action is exactly reconstructed from
half the diagonal of its genuine summed Hessian. -/
theorem globalMatterMultipletAction_eq_half_hessian
    (data : MatterMultipletActionData period hPeriod)
    (fields : MatterComponentFamily period hPeriod) :
    globalMatterMultipletAction period hPeriod data fields =
      (1 / 2 : Real) *
        globalMatterMultipletHessian period hPeriod data fields fields := by
  unfold globalMatterMultipletAction globalMatterMultipletHessian
  calc
    (∑ index : MatterComponentIndex,
        globalHolonomicScalarAction period hPeriod (data index).massSquared
          (data index).magnitude (fields index) (data index).measure) =
      ∑ index : MatterComponentIndex, (1 / 2 : Real) *
        weakGlobalHolonomicScalarJacobiOperator period hPeriod (data index)
          (fields index) (fields index) := by
        apply Finset.sum_congr rfl
        intro index _
        rw [← globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod
          (data index) (fields index) (fields index) (fields index)]
        exact globalHolonomicScalarAction_eq_half_actualMixedHessian period
          hPeriod (data index) (fields index) (fields index)
    _ = (1 / 2 : Real) * ∑ index : MatterComponentIndex,
        weakGlobalHolonomicScalarJacobiOperator period hPeriod (data index)
          (fields index) (fields index) := by
      rw [Finset.mul_sum]

/-- The same reconstruction for the eight fields extracted from one actual
Program-P configuration. -/
theorem globalIndependentMatterAction_eq_half_hessian
    (data : MatterMultipletActionData period hPeriod)
    (fields : P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.IndependentFields
      period hPeriod) :
    globalIndependentMatterAction period hPeriod data fields =
      (1 / 2 : Real) * globalMatterMultipletHessian period hPeriod data
        (P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D.independentMatterComponentFamily
          period hPeriod fields)
        (P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D.independentMatterComponentFamily
          period hPeriod fields) :=
  globalMatterMultipletAction_eq_half_hessian period hPeriod data
    (P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D.independentMatterComponentFamily
      period hPeriod fields)

end

end P0EFTJanusGlobalMatterMultipletActionReconstruction4D
end JanusFormal
