import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLLMeasureFieldTwoParameterDensity4D

/-! Raw finite-measure integration of the exact two-parameter LL density. -/

namespace JanusFormal
namespace P0EFTJanusLLMeasureFieldTwoParameterRawAction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev rawThroatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (rawThroatData period hPeriod)

local instance rawChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance rawIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance rawCompactSpace : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance rawMeasurableSpace : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance rawBorelSpace : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The explicit polynomial density is integrable for every finite raw measure. -/
theorem llMeasureFieldPolynomial_integrable
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (measureParameter fieldParameter : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (fun point =>
      llWorldvolumeDensity period hPeriod fields point +
        measureParameter * variation.measureDirection point * ‖fields.llField point‖ ^ 2 +
        2 * fieldParameter * fields.llMeasure point *
          inner Real (fields.llField point) (variation.fieldDirection point) +
        fieldParameter ^ 2 * fields.llMeasure point * ‖variation.fieldDirection point‖ ^ 2 +
        2 * measureParameter * fieldParameter * variation.measureDirection point *
          inner Real (fields.llField point) (variation.fieldDirection point) +
        measureParameter * fieldParameter ^ 2 * variation.measureDirection point *
          ‖variation.fieldDirection point‖ ^ 2) mu := by
  rw [← funext (llWorldvolumeDensity_twoParameter period hPeriod fields variation
    measureParameter fieldParameter)]
  exact llWorldvolumeDensity_integrable period hPeriod
    (llMeasureFieldCurve period hPeriod fields variation measureParameter fieldParameter) mu

/-- Exact raw integrated polynomial; no regularization or renormalized measure is asserted. -/
theorem globalLLAction_twoParameter_raw
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (measureParameter fieldParameter : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalLLAction period hPeriod
        (llMeasureFieldCurve period hPeriod fields variation
          measureParameter fieldParameter) mu =
      ∫ point,
        llWorldvolumeDensity period hPeriod fields point +
          measureParameter * variation.measureDirection point * ‖fields.llField point‖ ^ 2 +
          2 * fieldParameter * fields.llMeasure point *
            inner Real (fields.llField point) (variation.fieldDirection point) +
          fieldParameter ^ 2 * fields.llMeasure point * ‖variation.fieldDirection point‖ ^ 2 +
          2 * measureParameter * fieldParameter * variation.measureDirection point *
            inner Real (fields.llField point) (variation.fieldDirection point) +
          measureParameter * fieldParameter ^ 2 * variation.measureDirection point *
            ‖variation.fieldDirection point‖ ^ 2 ∂mu := by
  unfold globalLLAction
  congr 1
  funext point
  exact llWorldvolumeDensity_twoParameter period hPeriod fields variation
    measureParameter fieldParameter point

/-- The diagonal raw action has the integrated first-variation derivative. -/
theorem globalLLAction_twoParameter_diagonal_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real => globalLLAction period hPeriod
        (llMeasureFieldCurve period hPeriod fields variation epsilon epsilon) mu)
      (globalLLFirstVariation period hPeriod fields variation mu) 0 := by
  simpa [llMeasureFieldCurve, llAffineCurve] using
    globalLLAction_affine_hasDerivAt period hPeriod fields variation mu

end
end P0EFTJanusLLMeasureFieldTwoParameterRawAction4D
end JanusFormal
