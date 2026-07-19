import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTLLWorldvolumeHessian4D

/-! Integrated variational origin of the PT LL worldvolume Hessian. -/

namespace JanusFormal
namespace P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D

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
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegrableQuarticPolynomial

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

def ptLLFirstVariationDensity
    (fields : IndependentFields period hPeriod)
    (direction : LLVariation period hPeriod) :
    EffectiveThroat period hPeriod → Real :=
  ptAverage period hPeriod
    (llFirstVariationDensity period hPeriod fields direction)

def globalPTLLFirstVariation
    (fields : IndependentFields period hPeriod)
    (direction : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ p, ptLLFirstVariationDensity period hPeriod fields direction p ∂mu

private def remainderDensity
    (first second : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) : Real :=
  first.measureDirection p * ‖second.fieldDirection p‖ ^ 2 +
    2 * second.measureDirection p *
      inner Real (second.fieldDirection p) (first.fieldDirection p)

private def ptRemainderDensity
    (first second : LLVariation period hPeriod) :
    EffectiveThroat period hPeriod → Real :=
  ptAverage period hPeriod (remainderDensity period hPeriod first second)

private theorem ptFirstVariation_expansion
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod) (t : Real)
    (p : EffectiveThroat period hPeriod) :
    ptLLFirstVariationDensity period hPeriod
        (llMeasureFieldCurve period hPeriod fields second t t) first p =
      ptLLFirstVariationDensity period hPeriod fields first p +
        t * ptLLWorldvolumeHessianDensity period hPeriod fields first second p +
        t ^ 2 * ptRemainderDensity period hPeriod first second p := by
  unfold ptLLFirstVariationDensity ptLLWorldvolumeHessianDensity
    ptRemainderDensity ptAverage
  rw [llFirstVariationDensity_second_direction_expansion period hPeriod fields
      first second t p,
    llFirstVariationDensity_second_direction_expansion period hPeriod fields
      first second t (fixedThroatPT period hPeriod p)]
  unfold remainderDensity
  ring

private theorem ptLLFirstVariationDensity_integrable
    (fields : IndependentFields period hPeriod)
    (direction : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptLLFirstVariationDensity period hPeriod fields direction) mu := by
  have hraw := llFirstVariationDensity_continuous period hPeriod fields direction
  have h : Continuous (ptLLFirstVariationDensity period hPeriod fields direction) := by
    unfold ptLLFirstVariationDensity ptAverage
    exact continuous_const.mul (hraw.add
      (hraw.comp (continuous_fixedThroatPT period hPeriod)))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem ptRemainderDensity_integrable
    (first second : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptRemainderDensity period hPeriod first second) mu := by
  have hraw : Continuous (remainderDensity period hPeriod first second) := by
    unfold remainderDensity
    exact (first.measureDirection.contMDiff_toFun.continuous.mul
      (second.fieldDirection.contMDiff_toFun.continuous.norm.pow 2)).add
      ((continuous_const.mul second.measureDirection.contMDiff_toFun.continuous).mul
        (second.fieldDirection.contMDiff_toFun.continuous.inner
          first.fieldDirection.contMDiff_toFun.continuous))
  have h : Continuous (ptRemainderDensity period hPeriod first second) := by
    unfold ptRemainderDensity ptAverage
    exact continuous_const.mul (hraw.add
      (hraw.comp (continuous_fixedThroatPT period hPeriod)))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem globalPTLLFirstVariation_second_direction_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun t : Real => globalPTLLFirstVariation period hPeriod
        (llMeasureFieldCurve period hPeriod fields second t t) first mu)
      (globalPTLLWorldvolumeHessian period hPeriod fields first second mu) 0 := by
  have h0 := ptLLFirstVariationDensity_integrable period hPeriod fields first mu
  have h1 := ptLLWorldvolumeHessianDensity_integrable period hPeriod fields first second mu
  have h2 := ptRemainderDensity_integrable period hPeriod first second mu
  rw [show (fun t : Real => globalPTLLFirstVariation period hPeriod
      (llMeasureFieldCurve period hPeriod fields second t t) first mu) =
      fun t : Real =>
        (∫ p, ptLLFirstVariationDensity period hPeriod fields first p ∂mu) +
        t * (∫ p, ptLLWorldvolumeHessianDensity period hPeriod fields first second p ∂mu) +
        t ^ 2 * (∫ p, ptRemainderDensity period hPeriod first second p ∂mu) +
        t ^ 3 * (∫ _p, (0 : Real) ∂mu) + t ^ 4 * (∫ _p, (0 : Real) ∂mu) by
    funext t
    unfold globalPTLLFirstVariation
    simp_rw [ptFirstVariation_expansion period hPeriod fields first second t]
    simpa only [Pi.add_apply, mul_zero, add_zero] using integral_quartic mu _ _ _
      (fun _ : EffectiveThroat period hPeriod => (0 : Real))
      (fun _ : EffectiveThroat period hPeriod => (0 : Real))
      h0 h1 h2 (integrable_zero _ _ mu) (integrable_zero _ _ mu) t]
  unfold globalPTLLWorldvolumeHessian
  exact integral_quartic_hasDerivAt_zero mu
    (ptLLFirstVariationDensity period hPeriod fields first)
    (ptLLWorldvolumeHessianDensity period hPeriod fields first second)
    (ptRemainderDensity period hPeriod first second) (fun _ => 0) (fun _ => 0)

end
end P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D
end JanusFormal
