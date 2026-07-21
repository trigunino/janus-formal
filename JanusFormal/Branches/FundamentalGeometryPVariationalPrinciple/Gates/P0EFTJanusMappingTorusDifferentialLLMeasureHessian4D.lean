import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D

/-! Exact measure-field mixed variations of the differential LL density. -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusDifferentialLLMeasureHessian4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
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

/-- Affine variation of the independent LL measure-density field. -/
def differentialLLMeasureCurve
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod Real)
    (epsilon : Real) : IndependentFields period hPeriod :=
  { fields with llMeasure := fields.llMeasure + epsilon • direction }

/-- Its exact first-variation density. -/
def differentialLLMeasureFirstVariationDensity
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) : Real :=
  direction point * ‖fields.llField point‖ ^ 2

theorem differentialLLDensity_measureCurve_affine
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod Real)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    differentialLLDensity period hPeriod frame
        (differentialLLMeasureCurve period hPeriod fields direction epsilon) point =
      differentialLLDensity period hPeriod frame fields point +
        epsilon * differentialLLMeasureFirstVariationDensity period hPeriod
          fields direction point := by
  unfold differentialLLDensity differentialLLMeasureCurve
    differentialLLMeasureFirstVariationDensity llWorldvolumeDensity
    llFlux llAuxiliaryKineticWeight
  change _ + (fields.llMeasure point + epsilon * direction point) *
      ‖fields.llField point‖ ^ 2 = _
  ring

/-- The genuine mixed measure/flux Hessian density. -/
def differentialLLMeasureFluxHessianDensity
    (measureDirection : SmoothThroatField period hPeriod Real)
    (fluxDirection : SmoothThroatField period hPeriod LLFieldFiber)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  2 * measureDirection point *
    inner Real (fields.llField point) (fluxDirection point)

theorem measureFirstVariation_fluxCurve_quadratic
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (fluxDirection : SmoothThroatField period hPeriod LLFieldFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    differentialLLMeasureFirstVariationDensity period hPeriod
        (differentialLLFluxCurve period hPeriod fields fluxDirection epsilon)
        measureDirection point =
      differentialLLMeasureFirstVariationDensity period hPeriod fields
          measureDirection point +
        epsilon * differentialLLMeasureFluxHessianDensity period hPeriod
          measureDirection fluxDirection fields point +
        epsilon ^ 2 * measureDirection point * ‖fluxDirection point‖ ^ 2 := by
  unfold differentialLLMeasureFirstVariationDensity differentialLLFluxCurve
    differentialLLMeasureFluxHessianDensity
  change measureDirection point *
      ‖fields.llField point + epsilon • fluxDirection point‖ ^ 2 = _
  rw [norm_add_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem fluxFirstVariation_measureCurve_affine
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (fluxDirection : SmoothThroatField period hPeriod LLFieldFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    differentialLLFluxFirstVariationDensity period hPeriod frame
        (differentialLLMeasureCurve period hPeriod fields measureDirection epsilon)
        fluxDirection point =
      differentialLLFluxFirstVariationDensity period hPeriod frame fields
          fluxDirection point +
        epsilon * differentialLLMeasureFluxHessianDensity period hPeriod
          measureDirection fluxDirection fields point := by
  unfold differentialLLFluxFirstVariationDensity differentialLLMeasureCurve
    differentialLLMeasureFluxHessianDensity llAuxiliaryKineticWeight
  change _ + 2 * (fields.llMeasure point + epsilon * measureDirection point) * _ = _
  ring

/-- Measure and auxiliary metric occur in disjoint summands of this action. -/
theorem measureFirstVariation_auxMetricCurve_invariant
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (auxDirection : SmoothThroatField period hPeriod LLMetricFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    differentialLLMeasureFirstVariationDensity period hPeriod
        (differentialLLAuxMetricCurve period hPeriod fields auxDirection epsilon)
        measureDirection point =
      differentialLLMeasureFirstVariationDensity period hPeriod fields
        measureDirection point := by
  rfl

end

end P0EFTJanusMappingTorusDifferentialLLMeasureHessian4D
end JanusFormal
