import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLMixedZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D

namespace JanusFormal
namespace P0EFTJanusFullLLZeroActiveQuotientEnrichedD94D
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
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
open P0EFTJanusIntegratedPTFullLLFirstVariationZero4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

@[simp] theorem activeProjection_zeroFullDirection :
    activeProjection period hPeriod (zeroFullDirection period hPeriod) =
      zeroActiveDirection period hPeriod := by
  rfl

@[simp] theorem quotientHessian_zeroLLClass_left
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦zeroFullDirection period hPeriod⟧ ⟦direction⟧ = 0 := by
  rw [quotientHessian_mk]
  exact globalMatterRobinFullLLHessian_inactive_left period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields (zeroFullDirection period hPeriod) direction rfl

@[simp] theorem quotientHessian_zeroLLClass_right
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦direction⟧ ⟦zeroFullDirection period hPeriod⟧ = 0 := by
  rw [quotientHessian_mk]
  exact globalMatterRobinFullLLHessian_inactive_right period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields direction (zeroFullDirection period hPeriod) rfl

@[simp] theorem enrichedD9ActiveHessian_zeroLLObservation_left
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields (zeroFullDirection period hPeriod) sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point) = 0 := by
  rw [← fullHessian_eq_enrichedD9ActiveHessian]
  exact globalMatterRobinFullLLHessian_inactive_left period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields (zeroFullDirection period hPeriod) direction rfl

@[simp] theorem enrichedD9ActiveHessian_zeroLLObservation_right
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields (zeroFullDirection period hPeriod) sector column point) = 0 := by
  rw [← fullHessian_eq_enrichedD9ActiveHessian]
  exact globalMatterRobinFullLLHessian_inactive_right period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields direction (zeroFullDirection period hPeriod) rfl

end
end P0EFTJanusFullLLZeroActiveQuotientEnrichedD94D
end JanusFormal
