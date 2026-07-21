import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLMeasureHessian4D

/-! PT average of the exact LL measure/flux mixed Hessian. -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPTSymmetricDifferentialLLMeasureHessian4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusDifferentialLLMeasureHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def differentialLLMeasureDirectionPT
    (direction : SmoothThroatField period hPeriod Real) :
    SmoothThroatField period hPeriod Real :=
  throatPTPullback period hPeriod Real direction

/-- The actual two-element PT orbit average of the mixed density. -/
def ptSymmetricDifferentialLLMeasureFluxHessianDensity
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (fluxDirection : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) *
    (differentialLLMeasureFluxHessianDensity period hPeriod measureDirection
        fluxDirection fields point +
      differentialLLMeasureFluxHessianDensity period hPeriod
        (differentialLLMeasureDirectionPT period hPeriod measureDirection)
        (differentialLLFluxDirectionPT period hPeriod fluxDirection)
        (llPTPullback period hPeriod fields) point)

/-- The orbit formula is exactly the mean at `p` and `PT p`. -/
theorem ptSymmetricMeasureFluxHessianDensity_eq_point_average
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (fluxDirection : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLMeasureFluxHessianDensity period hPeriod fields
        measureDirection fluxDirection point =
      (1 / 2 : Real) *
        (differentialLLMeasureFluxHessianDensity period hPeriod measureDirection
            fluxDirection fields point +
          differentialLLMeasureFluxHessianDensity period hPeriod measureDirection
            fluxDirection fields (fixedThroatPT period hPeriod point)) := by
  rfl

/-- Differentiating first in the measure slot and then in the flux slot gives
the PT mixed density, including the exact quadratic remainder. -/
theorem ptMeasureFirstVariation_fluxCurves_quadratic
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (fluxDirection : SmoothThroatField period hPeriod LLFieldFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    (1 / 2 : Real) *
      (differentialLLMeasureFirstVariationDensity period hPeriod
          (differentialLLFluxCurve period hPeriod fields fluxDirection epsilon)
          measureDirection point +
        differentialLLMeasureFirstVariationDensity period hPeriod
          (differentialLLFluxCurve period hPeriod (llPTPullback period hPeriod fields)
            (differentialLLFluxDirectionPT period hPeriod fluxDirection) epsilon)
          (differentialLLMeasureDirectionPT period hPeriod measureDirection) point) =
    (1 / 2 : Real) *
      (differentialLLMeasureFirstVariationDensity period hPeriod fields
          measureDirection point +
        differentialLLMeasureFirstVariationDensity period hPeriod
          (llPTPullback period hPeriod fields)
          (differentialLLMeasureDirectionPT period hPeriod measureDirection) point) +
      epsilon * ptSymmetricDifferentialLLMeasureFluxHessianDensity period hPeriod
        fields measureDirection fluxDirection point +
      epsilon ^ 2 * (1 / 2 : Real) *
        (measureDirection point * ‖fluxDirection point‖ ^ 2 +
          differentialLLMeasureDirectionPT period hPeriod measureDirection point *
            ‖differentialLLFluxDirectionPT period hPeriod fluxDirection point‖ ^ 2) := by
  rw [measureFirstVariation_fluxCurve_quadratic,
    measureFirstVariation_fluxCurve_quadratic]
  unfold ptSymmetricDifferentialLLMeasureFluxHessianDensity
  ring

/-- Reversing the order of the two variations has the same PT coefficient. -/
theorem ptFluxFirstVariation_measureCurves_affine
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (fluxDirection : SmoothThroatField period hPeriod LLFieldFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    (1 / 2 : Real) *
      (differentialLLFluxFirstVariationDensity period hPeriod frame
          (differentialLLMeasureCurve period hPeriod fields measureDirection epsilon)
          fluxDirection point +
        differentialLLFluxFirstVariationDensity period hPeriod frame
          (differentialLLMeasureCurve period hPeriod (llPTPullback period hPeriod fields)
            (differentialLLMeasureDirectionPT period hPeriod measureDirection) epsilon)
          (differentialLLFluxDirectionPT period hPeriod fluxDirection) point) =
    (1 / 2 : Real) *
      (differentialLLFluxFirstVariationDensity period hPeriod frame fields
          fluxDirection point +
        differentialLLFluxFirstVariationDensity period hPeriod frame
          (llPTPullback period hPeriod fields)
          (differentialLLFluxDirectionPT period hPeriod fluxDirection) point) +
      epsilon * ptSymmetricDifferentialLLMeasureFluxHessianDensity period hPeriod
        fields measureDirection fluxDirection point := by
  rw [fluxFirstVariation_measureCurve_affine,
    fluxFirstVariation_measureCurve_affine]
  unfold ptSymmetricDifferentialLLMeasureFluxHessianDensity
  ring

/-- The measure/auxiliary-metric mixed variation remains zero after PT averaging. -/
theorem ptMeasureFirstVariation_auxMetricCurves_invariant
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (auxDirection : SmoothThroatField period hPeriod LLMetricFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    (1 / 2 : Real) *
      (differentialLLMeasureFirstVariationDensity period hPeriod
          (differentialLLAuxMetricCurve period hPeriod fields auxDirection epsilon)
          measureDirection point +
        differentialLLMeasureFirstVariationDensity period hPeriod
          (differentialLLAuxMetricCurve period hPeriod (llPTPullback period hPeriod fields)
            (differentialLLAuxMetricDirectionPT period hPeriod auxDirection) epsilon)
          (differentialLLMeasureDirectionPT period hPeriod measureDirection) point) =
    (1 / 2 : Real) *
      (differentialLLMeasureFirstVariationDensity period hPeriod fields
          measureDirection point +
        differentialLLMeasureFirstVariationDensity period hPeriod
          (llPTPullback period hPeriod fields)
          (differentialLLMeasureDirectionPT period hPeriod measureDirection) point) := by
  rw [measureFirstVariation_auxMetricCurve_invariant,
    measureFirstVariation_auxMetricCurve_invariant]

theorem ptSymmetricMeasureFluxHessianDensity_continuous
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (fluxDirection : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (ptSymmetricDifferentialLLMeasureFluxHessianDensity period hPeriod
      fields measureDirection fluxDirection) := by
  exact continuous_const.mul
    (((continuous_const.mul measureDirection.contMDiff_toFun.continuous).mul
      (fields.llField.contMDiff_toFun.continuous.inner
        fluxDirection.contMDiff_toFun.continuous)).add
      ((continuous_const.mul
        (differentialLLMeasureDirectionPT period hPeriod
          measureDirection).contMDiff_toFun.continuous).mul
        ((llPTPullback period hPeriod fields).llField.contMDiff_toFun.continuous.inner
          (differentialLLFluxDirectionPT period hPeriod
            fluxDirection).contMDiff_toFun.continuous)))

def globalPTSymmetricDifferentialLLMeasureFluxHessian
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (fluxDirection : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, ptSymmetricDifferentialLLMeasureFluxHessianDensity period hPeriod
    fields measureDirection fluxDirection point ∂mu

theorem ptSymmetricMeasureFluxHessianDensity_integrable
    (fields : IndependentFields period hPeriod)
    (measureDirection : SmoothThroatField period hPeriod Real)
    (fluxDirection : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptSymmetricDifferentialLLMeasureFluxHessianDensity period hPeriod
      fields measureDirection fluxDirection) mu :=
  (ptSymmetricMeasureFluxHessianDensity_continuous period hPeriod fields
    measureDirection fluxDirection).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end
end P0EFTJanusMappingTorusPTSymmetricDifferentialLLMeasureHessian4D
end JanusFormal
