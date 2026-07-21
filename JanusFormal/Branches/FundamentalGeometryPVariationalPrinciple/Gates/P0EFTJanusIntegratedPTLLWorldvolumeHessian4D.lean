import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D

/-! Integrated PT Hessian of the algebraic LL worldvolume term. -/

namespace JanusFormal
namespace P0EFTJanusIntegratedPTLLWorldvolumeHessian4D

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
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Mixed second derivative density for two complete LL directions. -/
def llWorldvolumeHessianDensity
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) : Real :=
  2 * first.measureDirection p *
      inner Real (fields.llField p) (second.fieldDirection p) +
    2 * second.measureDirection p *
      inner Real (fields.llField p) (first.fieldDirection p) +
    2 * fields.llMeasure p *
      inner Real (first.fieldDirection p) (second.fieldDirection p)

def ptLLWorldvolumeHessianDensity
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod) :
    EffectiveThroat period hPeriod → Real :=
  ptAverage period hPeriod
    (llWorldvolumeHessianDensity period hPeriod fields first second)

/-- The displayed Hessian is exactly the linear coefficient obtained by
varying the first-variation density in a distinct second direction. -/
theorem llFirstVariationDensity_second_direction_expansion
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod) (t : Real)
    (p : EffectiveThroat period hPeriod) :
    llFirstVariationDensity period hPeriod
        (llMeasureFieldCurve period hPeriod fields second t t) first p =
      llFirstVariationDensity period hPeriod fields first p +
        t * llWorldvolumeHessianDensity period hPeriod fields first second p +
        t ^ 2 * (first.measureDirection p * ‖second.fieldDirection p‖ ^ 2 +
          2 * second.measureDirection p *
            inner Real (second.fieldDirection p) (first.fieldDirection p)) := by
  change
    first.measureDirection p * ‖fields.llField p + t • second.fieldDirection p‖ ^ 2 +
      2 * (fields.llMeasure p + t * second.measureDirection p) *
        inner Real (fields.llField p + t • second.fieldDirection p)
          (first.fieldDirection p) = _
  rw [norm_add_sq_real]
  simp only [real_inner_smul_right, inner_add_left, real_inner_smul_left,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold llFirstVariationDensity llWorldvolumeHessianDensity
  rw [real_inner_comm (first.fieldDirection p) (second.fieldDirection p)]
  ring

theorem llWorldvolumeHessianDensity_symmetric
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod) :
    llWorldvolumeHessianDensity period hPeriod fields first second =
      llWorldvolumeHessianDensity period hPeriod fields second first := by
  funext p
  unfold llWorldvolumeHessianDensity
  rw [real_inner_comm (first.fieldDirection p) (second.fieldDirection p)]
  ring

theorem ptLLWorldvolumeHessianDensity_symmetric
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod) :
    ptLLWorldvolumeHessianDensity period hPeriod fields first second =
      ptLLWorldvolumeHessianDensity period hPeriod fields second first := by
  unfold ptLLWorldvolumeHessianDensity
  rw [llWorldvolumeHessianDensity_symmetric period hPeriod fields first second]

private theorem llWorldvolumeHessianDensity_continuous
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod) :
    Continuous (llWorldvolumeHessianDensity period hPeriod fields first second) := by
  unfold llWorldvolumeHessianDensity
  exact (((continuous_const.mul first.measureDirection.contMDiff_toFun.continuous).mul
    (fields.llField.contMDiff_toFun.continuous.inner
      second.fieldDirection.contMDiff_toFun.continuous)).add
    ((continuous_const.mul second.measureDirection.contMDiff_toFun.continuous).mul
      (fields.llField.contMDiff_toFun.continuous.inner
        first.fieldDirection.contMDiff_toFun.continuous))).add
    ((continuous_const.mul fields.llMeasure.contMDiff_toFun.continuous).mul
      (first.fieldDirection.contMDiff_toFun.continuous.inner
        second.fieldDirection.contMDiff_toFun.continuous))

theorem ptLLWorldvolumeHessianDensity_integrable
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptLLWorldvolumeHessianDensity period hPeriod fields first second) mu := by
  have hraw := llWorldvolumeHessianDensity_continuous period hPeriod fields first second
  have h : Continuous (ptLLWorldvolumeHessianDensity period hPeriod fields first second) := by
    unfold ptLLWorldvolumeHessianDensity ptAverage
    exact continuous_const.mul (hraw.add
      (hraw.comp (continuous_fixedThroatPT period hPeriod)))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def globalPTLLWorldvolumeHessian
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ p, ptLLWorldvolumeHessianDensity period hPeriod fields first second p ∂mu

theorem globalPTLLWorldvolumeHessian_symmetric
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTLLWorldvolumeHessian period hPeriod fields first second mu =
      globalPTLLWorldvolumeHessian period hPeriod fields second first mu := by
  unfold globalPTLLWorldvolumeHessian
  rw [ptLLWorldvolumeHessianDensity_symmetric period hPeriod fields first second]

end
end P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
end JanusFormal
