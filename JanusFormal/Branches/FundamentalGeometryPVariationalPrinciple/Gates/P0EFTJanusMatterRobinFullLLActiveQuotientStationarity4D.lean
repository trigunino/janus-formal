import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEulerReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientKernelReconstruction4D

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLActiveQuotientStationarity4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem quotientEuler_stationary_iff_activeEuler_stationary
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) (direction : ActiveQuotient period hPeriod) :
    quotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction direction = 0 ↔
      activeEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction (activeQuotientEquiv period hPeriod direction) = 0 := by
  rw [quotientEuler_eq_activeEuler_equiv]

theorem representativeEulerCurve_hasDerivAt_activeHessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure matter junction fields first second)
      (activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientEquiv period hPeriod (⟦first⟧ : ActiveQuotient period hPeriod))
        (activeQuotientEquiv period hPeriod (⟦second⟧ : ActiveQuotient period hPeriod))) 0 := by
  have h := representativeEulerCurve_hasDerivAt_quotientHessian period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first second
  rw [quotientHessian_mk, fullHessian_factors_active] at h
  simpa only [activeQuotientEquiv_mk] using h

end
end P0EFTJanusMatterRobinFullLLActiveQuotientStationarity4D
end JanusFormal
