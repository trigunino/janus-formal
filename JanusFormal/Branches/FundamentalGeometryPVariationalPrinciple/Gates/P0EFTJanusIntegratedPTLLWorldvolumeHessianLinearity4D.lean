import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTLLWorldvolumeHessian4D

namespace JanusFormal
namespace P0EFTJanusIntegratedPTLLWorldvolumeHessianLinearity4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def addVariation (first second : LLVariation period hPeriod) : LLVariation period hPeriod where
  measureDirection := first.measureDirection + second.measureDirection
  fieldDirection := first.fieldDirection + second.fieldDirection

def negVariation (variation : LLVariation period hPeriod) : LLVariation period hPeriod where
  measureDirection := -variation.measureDirection
  fieldDirection := -variation.fieldDirection

theorem llWorldvolumeHessianDensity_add_first
    (fields : IndependentFields period hPeriod)
    (first first' second : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) :
    llWorldvolumeHessianDensity period hPeriod fields
        (addVariation period hPeriod first first') second p =
      llWorldvolumeHessianDensity period hPeriod fields first second p +
        llWorldvolumeHessianDensity period hPeriod fields first' second p := by
  unfold llWorldvolumeHessianDensity addVariation
  change 2 * (first.measureDirection p + first'.measureDirection p) * _ +
    2 * _ * inner Real _ (first.fieldDirection p + first'.fieldDirection p) +
    2 * _ * inner Real (first.fieldDirection p + first'.fieldDirection p) _ = _
  rw [inner_add_right, inner_add_left]
  ring

theorem ptLLWorldvolumeHessianDensity_add_first
    (fields : IndependentFields period hPeriod)
    (first first' second : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) :
    ptLLWorldvolumeHessianDensity period hPeriod fields
        (addVariation period hPeriod first first') second p =
      ptLLWorldvolumeHessianDensity period hPeriod fields first second p +
        ptLLWorldvolumeHessianDensity period hPeriod fields first' second p := by
  unfold ptLLWorldvolumeHessianDensity ptAverage
  rw [llWorldvolumeHessianDensity_add_first, llWorldvolumeHessianDensity_add_first]
  ring

theorem globalPTLLWorldvolumeHessian_add_first
    (fields : IndependentFields period hPeriod)
    (first first' second : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTLLWorldvolumeHessian period hPeriod fields
        (addVariation period hPeriod first first') second mu =
      globalPTLLWorldvolumeHessian period hPeriod fields first second mu +
        globalPTLLWorldvolumeHessian period hPeriod fields first' second mu := by
  unfold globalPTLLWorldvolumeHessian
  rw [← integral_add
    (ptLLWorldvolumeHessianDensity_integrable period hPeriod fields first second mu)
    (ptLLWorldvolumeHessianDensity_integrable period hPeriod fields first' second mu)]
  apply integral_congr_ae
  filter_upwards [] with p
  exact ptLLWorldvolumeHessianDensity_add_first period hPeriod fields first first' second p

theorem llWorldvolumeHessianDensity_neg_first
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) :
    llWorldvolumeHessianDensity period hPeriod fields
        (negVariation period hPeriod first) second p =
      -llWorldvolumeHessianDensity period hPeriod fields first second p := by
  unfold llWorldvolumeHessianDensity negVariation
  change 2 * (-first.measureDirection p) * _ +
    2 * _ * inner Real _ (-first.fieldDirection p) +
    2 * _ * inner Real (-first.fieldDirection p) _ = _
  rw [inner_neg_right, inner_neg_left]
  ring

theorem ptLLWorldvolumeHessianDensity_neg_first
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) :
    ptLLWorldvolumeHessianDensity period hPeriod fields
        (negVariation period hPeriod first) second p =
      -ptLLWorldvolumeHessianDensity period hPeriod fields first second p := by
  unfold ptLLWorldvolumeHessianDensity ptAverage
  rw [llWorldvolumeHessianDensity_neg_first, llWorldvolumeHessianDensity_neg_first]
  ring

theorem globalPTLLWorldvolumeHessian_neg_first
    (fields : IndependentFields period hPeriod)
    (first second : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTLLWorldvolumeHessian period hPeriod fields
        (negVariation period hPeriod first) second mu =
      -globalPTLLWorldvolumeHessian period hPeriod fields first second mu := by
  unfold globalPTLLWorldvolumeHessian
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with p
  exact ptLLWorldvolumeHessianDensity_neg_first period hPeriod fields first second p

end
end P0EFTJanusIntegratedPTLLWorldvolumeHessianLinearity4D
end JanusFormal
