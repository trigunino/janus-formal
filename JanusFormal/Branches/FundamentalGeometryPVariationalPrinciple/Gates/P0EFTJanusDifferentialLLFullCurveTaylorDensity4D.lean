import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLHessianAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLLMeasureFieldTwoParameterDensity4D

/-! Exact quartic Taylor coefficients of the true differential LL density. -/

namespace JanusFormal
namespace P0EFTJanusDifferentialLLFullCurveTaylorDensity4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

def rawFullLLCubicDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) : Real :=
  inner Real (fields.llAuxMetric p) (dAux p) *
      throatDerivativeEnergy period hPeriod frame variation.fieldDirection p +
    ‖dAux p‖ ^ 2 * throatDerivativePairing period hPeriod frame
      fields.llField variation.fieldDirection p +
    llThirdVariationCoefficient period hPeriod variation p

def rawFullLLQuarticDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (p : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) * ‖dAux p‖ ^ 2 *
    throatDerivativeEnergy period hPeriod frame dField p

theorem differentialLLDensity_fullCurve_exact_taylor
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (variation : LLVariation period hPeriod) (t : Real)
    (p : EffectiveThroat period hPeriod) :
    differentialLLDensity period hPeriod frame
        (differentialLLFullCurve period hPeriod fields dAux
          variation.measureDirection variation.fieldDirection t) p =
      differentialLLDensity period hPeriod frame fields p +
      t * (differentialLLKineticFirstVariation period hPeriod frame
        fields.llAuxMetric fields.llField dAux variation.fieldDirection p +
        llFirstVariationDensity period hPeriod fields variation p) +
      t ^ 2 * ((1 / 2 : Real) *
        differentialLLKineticMixedHessianDensity period hPeriod frame
          fields.llAuxMetric fields.llField dAux dAux
          variation.fieldDirection variation.fieldDirection p +
        llSecondVariationCoefficient period hPeriod fields variation p) +
      t ^ 3 * rawFullLLCubicDensity period hPeriod frame fields dAux variation p +
      t ^ 4 * rawFullLLQuarticDensity period hPeriod frame dAux
        variation.fieldDirection p := by
  unfold differentialLLFullCurve
  unfold differentialLLDensity
  unfold llAuxiliaryKineticWeight
  rw [← show differentialLLKineticDensity period hPeriod frame
      (fields.llAuxMetric + t • dAux) (fields.llField + t • variation.fieldDirection) p =
      (1 / 2 : Real) * (1 + ‖(fields.llAuxMetric + t • dAux) p‖ ^ 2) *
        throatDerivativeEnergy period hPeriod frame
          (fields.llField + t • variation.fieldDirection) p by rfl]
  rw [← show differentialLLKineticDensity period hPeriod frame
      fields.llAuxMetric fields.llField p =
      (1 / 2 : Real) * (1 + ‖fields.llAuxMetric p‖ ^ 2) *
        throatDerivativeEnergy period hPeriod frame fields.llField p by rfl]
  rw [differentialLLKineticDensity_simultaneous_polynomial]
  rw [show llWorldvolumeDensity period hPeriod
      { fields with
        llAuxMetric := fields.llAuxMetric + t • dAux
        llMeasure := fields.llMeasure + t • variation.measureDirection
        llField := fields.llField + t • variation.fieldDirection } p =
      llWorldvolumeDensity period hPeriod
        (llMeasureFieldCurve period hPeriod fields variation t t) p by rfl]
  rw [llWorldvolumeDensity_twoParameter]
  unfold differentialLLKineticFirstVariation
    differentialLLKineticMixedHessianDensity rawFullLLCubicDensity
    rawFullLLQuarticDensity llFirstVariationDensity
    llSecondVariationCoefficient llThirdVariationCoefficient
  rw [throatDerivativePairing_self_eq_energy period hPeriod frame
      variation.fieldDirection p,
    real_inner_self_eq_norm_sq]
  unfold differentialLLKineticDensity llWorldvolumeDensity llFlux
  ring

end
end P0EFTJanusDifferentialLLFullCurveTaylorDensity4D
end JanusFormal
