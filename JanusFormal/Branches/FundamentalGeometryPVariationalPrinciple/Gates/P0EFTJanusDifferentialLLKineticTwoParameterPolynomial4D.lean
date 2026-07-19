import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D

/-! Exact bivariate polynomial of the raw differential LL kinetic density. -/

namespace JanusFormal
namespace P0EFTJanusDifferentialLLKineticTwoParameterPolynomial4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The genuine two-direction affine surface in the kinetic field slots. -/
def differentialLLKineticTwoParameterDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (s t : Real) (point : EffectiveThroat period hPeriod) : Real :=
  differentialLLKineticDensity period hPeriod frame
    ((aux + s • dAux₁) + t • dAux₂)
    ((field + s • dField₁) + t • dField₂) point

theorem differentialLLKineticTwoParameterDensity_polynomial
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (s t : Real) (point : EffectiveThroat period hPeriod) :
    differentialLLKineticTwoParameterDensity period hPeriod frame aux field
        dAux₁ dAux₂ dField₁ dField₂ s t point =
      (1 / 2 : Real) *
        ((1 + ‖aux point‖ ^ 2) +
          s * (2 * inner Real (aux point) (dAux₁ point)) +
          t * (2 * inner Real (aux point) (dAux₂ point)) +
          s ^ 2 * ‖dAux₁ point‖ ^ 2 +
          t ^ 2 * ‖dAux₂ point‖ ^ 2 +
          s * t * (2 * inner Real (dAux₁ point) (dAux₂ point))) *
        (throatDerivativeEnergy period hPeriod frame field point +
          s * (2 * throatDerivativePairing period hPeriod frame field dField₁ point) +
          t * (2 * throatDerivativePairing period hPeriod frame field dField₂ point) +
          s ^ 2 * throatDerivativeEnergy period hPeriod frame dField₁ point +
          t ^ 2 * throatDerivativeEnergy period hPeriod frame dField₂ point +
          s * t * (2 * throatDerivativePairing period hPeriod frame dField₁ dField₂ point)) := by
  have hDerivative (index : Fin frame.count) :
      throatFrameDerivative period hPeriod LLFieldFiber frame
          ((field + s • dField₁) + t • dField₂) point index =
        (throatFrameDerivative period hPeriod LLFieldFiber frame field point index +
          s • throatFrameDerivative period hPeriod LLFieldFiber frame dField₁ point index) +
          t • throatFrameDerivative period hPeriod LLFieldFiber frame dField₂ point index := by
    rw [congrFun (congrFun (throatFrameDerivative_add period hPeriod LLFieldFiber
      frame (field + s • dField₁) (t • dField₂)) point) index]
    simp only [Pi.add_apply]
    rw [congrFun (congrFun (throatFrameDerivative_add period hPeriod LLFieldFiber
      frame field (s • dField₁)) point) index]
    simp only [Pi.add_apply]
    rw [congrFun (congrFun (throatFrameDerivative_smul period hPeriod LLFieldFiber
      frame s dField₁) point) index]
    rw [congrFun (congrFun (throatFrameDerivative_smul period hPeriod LLFieldFiber
      frame t dField₂) point) index]
    rfl
  have hAux :
      1 + ‖(aux point + s • dAux₁ point) + t • dAux₂ point‖ ^ 2 =
        (1 + ‖aux point‖ ^ 2) +
          s * (2 * inner Real (aux point) (dAux₁ point)) +
          t * (2 * inner Real (aux point) (dAux₂ point)) +
          s ^ 2 * ‖dAux₁ point‖ ^ 2 + t ^ 2 * ‖dAux₂ point‖ ^ 2 +
          s * t * (2 * inner Real (dAux₁ point) (dAux₂ point)) := by
    rw [norm_add_sq_real, norm_add_sq_real]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hEnergy :
      throatDerivativeEnergy period hPeriod frame
          ((field + s • dField₁) + t • dField₂) point =
        throatDerivativeEnergy period hPeriod frame field point +
          s * (2 * throatDerivativePairing period hPeriod frame field dField₁ point) +
          t * (2 * throatDerivativePairing period hPeriod frame field dField₂ point) +
          s ^ 2 * throatDerivativeEnergy period hPeriod frame dField₁ point +
          t ^ 2 * throatDerivativeEnergy period hPeriod frame dField₂ point +
          s * t * (2 * throatDerivativePairing period hPeriod frame dField₁ dField₂ point) := by
    unfold throatDerivativeEnergy throatDerivativePairing
    simp_rw [hDerivative, norm_add_sq_real, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [inner_add_left, real_inner_smul_left,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  unfold differentialLLKineticTwoParameterDensity differentialLLKineticDensity
  change (1 / 2 : Real) *
    (1 + ‖(aux point + s • dAux₁ point) + t • dAux₂ point‖ ^ 2) * _ = _
  rw [hAux, hEnergy]

/-- The algebraic coefficient of the monomial `s*t` in the displayed product. -/
def differentialLLKineticSTCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) *
    ((1 + ‖aux point‖ ^ 2) *
        (2 * throatDerivativePairing period hPeriod frame dField₁ dField₂ point) +
      (2 * inner Real (aux point) (dAux₁ point)) *
        (2 * throatDerivativePairing period hPeriod frame field dField₂ point) +
      (2 * inner Real (aux point) (dAux₂ point)) *
        (2 * throatDerivativePairing period hPeriod frame field dField₁ point) +
      (2 * inner Real (dAux₁ point) (dAux₂ point)) *
        throatDerivativeEnergy period hPeriod frame field point)

theorem differentialLLKineticSTCoefficient_eq_mixedHessianDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    differentialLLKineticSTCoefficient period hPeriod frame aux field
        dAux₁ dAux₂ dField₁ dField₂ point =
      differentialLLKineticMixedHessianDensity period hPeriod frame aux field
        dAux₁ dAux₂ dField₁ dField₂ point := by
  unfold differentialLLKineticSTCoefficient
    differentialLLKineticMixedHessianDensity
  ring

end
end P0EFTJanusDifferentialLLKineticTwoParameterPolynomial4D
end JanusFormal
