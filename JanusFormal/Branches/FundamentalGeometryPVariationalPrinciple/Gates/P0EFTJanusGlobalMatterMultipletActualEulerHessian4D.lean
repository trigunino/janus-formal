import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D

namespace JanusFormal
namespace P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Analytic action data for each of the actual eight matter coordinates. -/
abbrev MatterMultipletActionData :=
  MatterComponentIndex → GlobalHolonomicScalarFormData period hPeriod

/-- Componentwise affine curve on the complete matter multiplet. -/
def matterMultipletAffineCurve
    (fields directions : MatterComponentFamily period hPeriod)
    (epsilon : Real) : MatterComponentFamily period hPeriod :=
  fun index => scalarAffineCurve period hPeriod (fields index)
    (directions index) epsilon

/-- Sum of the eight unchanged global scalar actions on the genuine matter
components of the Program-P field package. -/
def globalMatterMultipletAction
    (data : MatterMultipletActionData period hPeriod)
    (fields : MatterComponentFamily period hPeriod) : Real :=
  ∑ index : MatterComponentIndex,
    globalHolonomicScalarAction period hPeriod (data index).massSquared
      (data index).magnitude (fields index) (data index).measure

/-- The action evaluated on the eight fields extracted from one actual
`IndependentFields` configuration. -/
def globalIndependentMatterAction
    (data : MatterMultipletActionData period hPeriod)
    (fields : IndependentFields period hPeriod) : Real :=
  globalMatterMultipletAction period hPeriod data
    (independentMatterComponentFamily period hPeriod fields)

/-- Exact weak Euler pairing of the eight-component action. -/
def globalMatterMultipletEuler
    (data : MatterMultipletActionData period hPeriod)
    (fields directions : MatterComponentFamily period hPeriod) : Real :=
  ∑ index : MatterComponentIndex,
    weakGlobalHolonomicScalarEulerOperator period hPeriod (data index)
      (fields index) (directions index)

/-- The summed Euler pairing is the genuine first derivative of the single
eight-component matter action. -/
theorem globalMatterMultipletAction_hasDerivAt
    (data : MatterMultipletActionData period hPeriod)
    (fields directions : MatterComponentFamily period hPeriod) :
    HasDerivAt
      (fun epsilon : Real => globalMatterMultipletAction period hPeriod data
        (matterMultipletAffineCurve period hPeriod fields directions epsilon))
      (globalMatterMultipletEuler period hPeriod data fields directions) 0 := by
  unfold globalMatterMultipletAction globalMatterMultipletEuler
    matterMultipletAffineCurve
  exact HasDerivAt.fun_sum fun index _ =>
    globalHolonomicScalarAction_hasDerivAt_weakEuler period hPeriod
      (data index) (fields index) (directions index)

/-- Exact Jacobi/Hessian pairing of the eight-component action. -/
def globalMatterMultipletHessian
    (data : MatterMultipletActionData period hPeriod)
    (first second : MatterComponentFamily period hPeriod) : Real :=
  ∑ index : MatterComponentIndex,
    weakGlobalHolonomicScalarJacobiOperator period hPeriod (data index)
      (first index) (second index)

/-- The multiplet Euler is genuinely differentiable and its derivative is the
summed Hessian of the same action. -/
theorem globalMatterMultipletEuler_hasDerivAt
    (data : MatterMultipletActionData period hPeriod)
    (fields first second : MatterComponentFamily period hPeriod) :
    HasDerivAt
      (fun epsilon : Real => globalMatterMultipletEuler period hPeriod data
        (matterMultipletAffineCurve period hPeriod fields first epsilon) second)
      (globalMatterMultipletHessian period hPeriod data first second) 0 := by
  unfold globalMatterMultipletEuler globalMatterMultipletHessian
    matterMultipletAffineCurve
  exact HasDerivAt.fun_sum fun index _ =>
    weakGlobalHolonomicScalarEulerOperator_hasDerivAt period hPeriod
      (data index) (fields index) (first index) (second index)

/-- Helmholtz symmetry for the actual eight-component matter Hessian. -/
theorem globalMatterMultipletHessian_symmetric
    (data : MatterMultipletActionData period hPeriod)
    (first second : MatterComponentFamily period hPeriod) :
    globalMatterMultipletHessian period hPeriod data first second =
      globalMatterMultipletHessian period hPeriod data second first := by
  unfold globalMatterMultipletHessian
  apply Finset.sum_congr rfl
  intro index _
  exact weakGlobalHolonomicScalarJacobiOperator_symmetric period hPeriod
    (data index) (first index) (second index)

end

end P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
end JanusFormal
