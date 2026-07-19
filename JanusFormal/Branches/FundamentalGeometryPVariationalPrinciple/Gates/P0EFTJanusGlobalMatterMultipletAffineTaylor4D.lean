import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalMatterMultipletActionReconstruction4D

namespace JanusFormal
namespace P0EFTJanusGlobalMatterMultipletAffineTaylor4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Exact quadratic Taylor formula for the genuine eight-component matter
action along its common affine curve. -/
theorem globalMatterMultipletAction_affine_exact_taylor
    (data : MatterMultipletActionData period hPeriod)
    (fields directions : MatterComponentFamily period hPeriod) (t : Real) :
    globalMatterMultipletAction period hPeriod data
        (matterMultipletAffineCurve period hPeriod fields directions t) =
      globalMatterMultipletAction period hPeriod data fields +
      t * globalMatterMultipletEuler period hPeriod data fields directions +
      (t ^ 2 / 2) * globalMatterMultipletHessian period hPeriod data
        directions directions := by
  unfold globalMatterMultipletAction matterMultipletAffineCurve
    globalMatterMultipletEuler globalMatterMultipletHessian
  simp_rw [globalHolonomicScalarAction_affine period hPeriod
    (data _).massSquared (data _).magnitude (fields _) (directions _)
    (data _).measure ((data _).variationContract period hPeriod (fields _)
      (directions _)) t]
  simp_rw [weakGlobalHolonomicScalarEulerOperator_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.mul_sum]
  congr 2
  funext index
  rw [show globalHolonomicScalarAction period hPeriod (data index).massSquared
      (data index).magnitude (directions index) (data index).measure =
      (1 / 2 : Real) * weakGlobalHolonomicScalarJacobiOperator period hPeriod
        (data index) (directions index) (directions index) by
    rw [← globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod
      (data index) (directions index) (directions index) (directions index)]
    exact P0EFTJanusGlobalHolonomicScalarActionReconstruction4D.globalHolonomicScalarAction_eq_half_actualMixedHessian
      period hPeriod (data index) (directions index) (directions index)]
  ring

end
end P0EFTJanusGlobalMatterMultipletAffineTaylor4D
end JanusFormal
