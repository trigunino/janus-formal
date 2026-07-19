import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLMixedActiveQuotient4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- The genuine mixed Taylor coefficient depends only on the two active
projections, hence is unchanged by replacing either full direction with an
actively equivalent one. -/
theorem fullMatterRobinTrueLLMixedTaylorCoefficient_factors_active
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first first' second second' : FullMatterRobinLLDirections period hPeriod)
    (hFirst : activeProjection period hPeriod first =
      activeProjection period hPeriod first')
    (hSecond : activeProjection period hPeriod second =
      activeProjection period hPeriod second') :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus
        kMinus robinMeasure frame llMeasure fields first second =
      fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData
        kPlus kMinus robinMeasure frame llMeasure fields first' second' := by
  rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
    fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
    fullHessian_factors_active, fullHessian_factors_active, hFirst, hSecond]

/-- On quotient classes the same mixed coefficient is exactly the descended
active quotient Hessian, not a separate reduced model. -/
theorem fullMatterRobinTrueLLMixedTaylorCoefficient_eq_quotientHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus
        kMinus robinMeasure frame llMeasure fields first second =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields ⟦first⟧ ⟦second⟧ := by
  rw [quotientHessian_mk,
    fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian]

end
end P0EFTJanusFullMatterRobinTrueLLMixedActiveQuotient4D
end JanusFormal
