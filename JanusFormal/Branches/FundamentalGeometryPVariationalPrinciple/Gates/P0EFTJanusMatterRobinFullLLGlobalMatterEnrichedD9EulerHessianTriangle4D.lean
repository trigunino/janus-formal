import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Euler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D

/-! The true representative Euler curve differentiates to the D9-factorized true Hessian. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9EulerHessianTriangle4D
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
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem representativeEulerCurve_hasDerivAt_enrichedD9ActiveHessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod) (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure matter junction fields first second)
      (enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point)) 0 := by
  have h := representativeEulerCurve_hasDerivAt_quotientHessian period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first second
  rw [quotientHessian_mk, fullHessian_eq_enrichedD9ActiveHessian] at h
  exact h

end
end P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9EulerHessianTriangle4D
end JanusFormal
