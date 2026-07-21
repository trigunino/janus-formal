import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGhostAuxiliaryTranslationInvariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActiveQuotientDerivatives4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedCoefficientActiveQuotientDerivatives4D

namespace JanusFormal
namespace P0EFTJanusGhostAuxiliaryMixedTranslationInvariance4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
open P0EFTJanusFullMatterRobinTrueLLMixedActiveQuotient4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLMixedCoefficientActiveQuotientDerivatives4D
open P0EFTJanusGhostAuxiliaryTranslationInvariance4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

variable (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
  (robinMeasure : Measure (EffectiveThroat period hPeriod))
  (frame : SmoothThroatGeneratingFrame period hPeriod)
  (llMeasure : Measure (EffectiveThroat period hPeriod))
  (fields : IndependentFields period hPeriod)
  (first second : FullMatterRobinLLDirections period hPeriod)

private theorem mixed_congr (first' second' : FullMatterRobinLLDirections period hPeriod)
    (hFirst : activeProjection period hPeriod first' = activeProjection period hPeriod first)
    (hSecond : activeProjection period hPeriod second' = activeProjection period hPeriod second) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields first' second' =
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields first second :=
  fullMatterRobinTrueLLMixedTaylorCoefficient_factors_active period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields first' first second' second hFirst hSecond

theorem addGhost_mixed_first (ghost) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields (addGhost period hPeriod first ghost) second =
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields first second :=
  mixed_congr period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second
    _ _ (addGhost_activeProjection period hPeriod first ghost) rfl

theorem addGhost_mixed_second (ghost) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields first (addGhost period hPeriod second ghost) =
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields first second :=
  mixed_congr period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second
    _ _ rfl (addGhost_activeProjection period hPeriod second ghost)

theorem addAuxiliary_mixed_first (auxiliary) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields (addAuxiliary period hPeriod first auxiliary) second =
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields first second :=
  mixed_congr period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second
    _ _ (addAuxiliary_activeProjection period hPeriod first auxiliary) rfl

theorem addAuxiliary_mixed_second (auxiliary) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields first (addAuxiliary period hPeriod second auxiliary) =
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields first second :=
  mixed_congr period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second
    _ _ rfl (addAuxiliary_activeProjection period hPeriod second auxiliary)

theorem addGhost_hessian_first (ghost) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields (addGhost period hPeriod first ghost) second =
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields first second := by
  rw [fullHessian_factors_active, fullHessian_factors_active, addGhost_activeProjection]

theorem addGhost_hessian_second (ghost) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields first (addGhost period hPeriod second ghost) =
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields first second := by
  rw [fullHessian_factors_active, fullHessian_factors_active, addGhost_activeProjection]

theorem addAuxiliary_hessian_first (auxiliary) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields (addAuxiliary period hPeriod first auxiliary) second =
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields first second := by
  rw [fullHessian_factors_active, fullHessian_factors_active, addAuxiliary_activeProjection]

theorem addAuxiliary_hessian_second (auxiliary) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields first (addAuxiliary period hPeriod second auxiliary) =
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields first second := by
  rw [fullHessian_factors_active, fullHessian_factors_active, addAuxiliary_activeProjection]

variable (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
  [IsFiniteMeasure robinMeasure] [IsFiniteMeasure llMeasure]
  (matter : MatterComponentFamily period hPeriod)
  (junction : SmoothThroatField period hPeriod Real)

theorem addGhost_eulerMixed_first (ghost) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure matter junction fields (addGhost period hPeriod first ghost) second)
      (fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second) 0 := by
  simpa [addGhost_mixed_first period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
    fields first second ghost] using
    representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields
        (addGhost period hPeriod first ghost) second

theorem addGhost_eulerMixed_second (ghost) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure matter junction fields first (addGhost period hPeriod second ghost))
      (fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second) 0 := by
  simpa [addGhost_mixed_second period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
    fields first second ghost] using
    representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first
        (addGhost period hPeriod second ghost)

theorem addAuxiliary_eulerMixed_first (auxiliary) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure matter junction fields (addAuxiliary period hPeriod first auxiliary) second)
      (fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second) 0 := by
  simpa [addAuxiliary_mixed_first period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
    fields first second auxiliary] using
    representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields
        (addAuxiliary period hPeriod first auxiliary) second

theorem addAuxiliary_eulerMixed_second (auxiliary) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure matter junction fields first (addAuxiliary period hPeriod second auxiliary))
      (fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second) 0 := by
  simpa [addAuxiliary_mixed_second period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
    fields first second auxiliary] using
    representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first
        (addAuxiliary period hPeriod second auxiliary)

end
end P0EFTJanusGhostAuxiliaryMixedTranslationInvariance4D
end JanusFormal
