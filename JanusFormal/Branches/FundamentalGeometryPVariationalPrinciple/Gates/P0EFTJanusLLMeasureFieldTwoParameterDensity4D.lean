import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalLLVariation4D

/-!
# Two-parameter measure/field expansion of the LL density

This is the actual algebraic density `llMeasure * ‖llField‖²`, with measure
and field varied by independent real parameters.  No integration or global
claim is made.
-/

namespace JanusFormal
namespace P0EFTJanusLLMeasureFieldTwoParameterDensity4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Independent measure and field parameters in the actual LL packet. -/
def llMeasureFieldCurve
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (measureParameter fieldParameter : Real) :
    IndependentFields period hPeriod :=
  { fields with
    llMeasure := fields.llMeasure +
      measureParameter • variation.measureDirection
    llField := fields.llField + fieldParameter • variation.fieldDirection }

/-- Exact two-parameter expansion, displaying both mixed monomials. -/
theorem llWorldvolumeDensity_twoParameter
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (measureParameter fieldParameter : Real)
    (point : EffectiveThroat period hPeriod) :
    llWorldvolumeDensity period hPeriod
        (llMeasureFieldCurve period hPeriod fields variation
          measureParameter fieldParameter) point =
      llWorldvolumeDensity period hPeriod fields point +
        measureParameter * variation.measureDirection point *
          ‖fields.llField point‖ ^ 2 +
        2 * fieldParameter * fields.llMeasure point *
          inner Real (fields.llField point) (variation.fieldDirection point) +
        fieldParameter ^ 2 * fields.llMeasure point *
          ‖variation.fieldDirection point‖ ^ 2 +
        2 * measureParameter * fieldParameter *
          variation.measureDirection point *
          inner Real (fields.llField point) (variation.fieldDirection point) +
        measureParameter * fieldParameter ^ 2 *
          variation.measureDirection point *
          ‖variation.fieldDirection point‖ ^ 2 := by
  change
    (fields.llMeasure point +
        measureParameter * variation.measureDirection point) *
      ‖fields.llField point +
        fieldParameter • variation.fieldDirection point‖ ^ 2 = _
  rw [norm_add_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]
  unfold llWorldvolumeDensity llFlux
  ring

/-- On the diagonal parameter this polynomial has the genuine pointwise
first derivative already encoded by `llFirstVariationDensity`. -/
theorem llWorldvolumeDensity_affine_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    HasDerivAt
      (fun epsilon : Real =>
        llWorldvolumeDensity period hPeriod
          (llMeasureFieldCurve period hPeriod fields variation epsilon epsilon)
          point)
      (llFirstVariationDensity period hPeriod fields variation point) 0 := by
  rw [show (fun epsilon : Real =>
      llWorldvolumeDensity period hPeriod
        (llMeasureFieldCurve period hPeriod fields variation epsilon epsilon)
        point) =
      (fun epsilon : Real =>
        llWorldvolumeDensity period hPeriod fields point +
          epsilon * llFirstVariationDensity period hPeriod fields variation point +
          epsilon ^ 2 * llSecondVariationCoefficient period hPeriod fields
            variation point +
          epsilon ^ 3 * llThirdVariationCoefficient period hPeriod variation
            point) from by
    funext epsilon
    rw [llWorldvolumeDensity_twoParameter]
    unfold llFirstVariationDensity llSecondVariationCoefficient
      llThirdVariationCoefficient
    ring]
  have hDerivative :=
    ((hasDerivAt_const (x := (0 : Real))
      (llWorldvolumeDensity period hPeriod fields point)).add
      (((hasDerivAt_id (x := (0 : Real))).mul_const
        (llFirstVariationDensity period hPeriod fields variation point)).add
        ((((hasDerivAt_id (x := (0 : Real))).pow 2).mul_const
          (llSecondVariationCoefficient period hPeriod fields variation point)).add
          (((hasDerivAt_id (x := (0 : Real))).pow 3).mul_const
            (llThirdVariationCoefficient period hPeriod variation point)))))
  have hFunction :
      ((fun _ : Real => llWorldvolumeDensity period hPeriod fields point) +
        ((fun epsilon : Real => epsilon *
          llFirstVariationDensity period hPeriod fields variation point) +
          ((fun epsilon : Real => epsilon ^ 2 *
            llSecondVariationCoefficient period hPeriod fields variation point) +
            (fun epsilon : Real => epsilon ^ 3 *
              llThirdVariationCoefficient period hPeriod variation point)))) =
        (fun epsilon : Real =>
          llWorldvolumeDensity period hPeriod fields point +
            epsilon * llFirstVariationDensity period hPeriod fields variation point +
            epsilon ^ 2 * llSecondVariationCoefficient period hPeriod fields
              variation point +
            epsilon ^ 3 * llThirdVariationCoefficient period hPeriod variation point) := by
    funext epsilon
    simp only [Pi.add_apply]
    ring
  rw [← hFunction]
  simpa [id] using hDerivative

end

end P0EFTJanusLLMeasureFieldTwoParameterDensity4D
end JanusFormal
