import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinLLDirections4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

/-! Exact pointwise simultaneous variation of the differential LL kinetic term. -/

namespace JanusFormal
namespace P0EFTJanusDifferentialLLKineticSimultaneousVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The kinetic summand of the actual differential LL density. -/
def differentialLLKineticDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) * (1 + ‖aux point‖ ^ 2) *
    throatDerivativeEnergy period hPeriod frame field point

/-- Exact factored quartic expansion along the simultaneous affine line. -/
theorem differentialLLKineticDensity_simultaneous_polynomial
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (t : Real) (point : EffectiveThroat period hPeriod) :
    differentialLLKineticDensity period hPeriod frame
        (aux + t • dAux) (field + t • dField) point =
      (1 / 2 : Real) *
        ((1 + ‖aux point‖ ^ 2) +
          t * (2 * inner Real (aux point) (dAux point)) +
          t ^ 2 * ‖dAux point‖ ^ 2) *
        (throatDerivativeEnergy period hPeriod frame field point +
          t * (2 * throatDerivativePairing period hPeriod frame field dField point) +
          t ^ 2 * throatDerivativeEnergy period hPeriod frame dField point) := by
  have hDerivative (index : Fin frame.count) :
      throatFrameDerivative period hPeriod LLFieldFiber frame
          (field + t • dField) point index =
        throatFrameDerivative period hPeriod LLFieldFiber frame field point index +
          t • throatFrameDerivative period hPeriod LLFieldFiber frame dField point index := by
    rw [congrFun (congrFun
      (throatFrameDerivative_add period hPeriod LLFieldFiber frame field
        (t • dField)) point) index]
    simp only [Pi.add_apply]
    rw [congrFun (congrFun
      (throatFrameDerivative_smul period hPeriod LLFieldFiber frame t dField)
        point) index]
    rfl
  unfold differentialLLKineticDensity throatDerivativeEnergy
    throatDerivativePairing
  simp_rw [hDerivative, norm_add_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  change (1 / 2 : Real) *
      (1 + ‖aux point + t • dAux point‖ ^ 2) * _ = _
  rw [norm_add_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

/-- The genuine linear coefficient: flux response plus auxiliary-metric response. -/
def differentialLLKineticFirstVariation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 + ‖aux point‖ ^ 2) *
      throatDerivativePairing period hPeriod frame field dField point +
    inner Real (aux point) (dAux point) *
      throatDerivativeEnergy period hPeriod frame field point

/- The exact polynomial theorem above identifies this as the coefficient of
`t`; its integrated differentiation is deliberately left to a later gate. -/
theorem differentialLLKineticFirstVariation_eq_linearCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    differentialLLKineticFirstVariation period hPeriod frame aux field
        dAux dField point =
      (1 / 2 : Real) *
        ((1 + ‖aux point‖ ^ 2) *
            (2 * throatDerivativePairing period hPeriod frame field dField point) +
          (2 * inner Real (aux point) (dAux point)) *
            throatDerivativeEnergy period hPeriod frame field point) := by
  unfold differentialLLKineticFirstVariation
  ring

end

end P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
end JanusFormal
