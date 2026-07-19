import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Euler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEulerReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientKernelReconstruction4D

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ActiveQuotientBridge4D
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
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerReconstruction4D
open P0EFTJanusMatterRobinFullLLActiveQuotientKernelReconstruction4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Euler4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def enrichedD9ActiveQuotientClass (packet : GlobalMatterEnrichedD9Projection period hPeriod) :
    ActiveQuotient period hPeriod :=
  (activeQuotientEquiv period hPeriod).symm (toActiveDirection period hPeriod packet)

@[simp] theorem activeQuotientEquiv_enrichedD9ActiveQuotientClass
    (packet : GlobalMatterEnrichedD9Projection period hPeriod) :
    activeQuotientEquiv period hPeriod (enrichedD9ActiveQuotientClass period hPeriod packet) =
      toActiveDirection period hPeriod packet := by
  exact Equiv.apply_symm_apply _ _

theorem quotientHessian_enrichedD9_classes
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (first second : GlobalMatterEnrichedD9Projection period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (enrichedD9ActiveQuotientClass period hPeriod first)
        (enrichedD9ActiveQuotientClass period hPeriod second) =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second := by
  rw [quotientHessian_eq_activeHessian_equiv]
  simp [enrichedD9ActiveQuotientClass, enrichedD9ActiveHessian]

theorem quotientEuler_enrichedD9_class
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (packet : GlobalMatterEnrichedD9Projection period hPeriod) :
    quotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        fields junction (enrichedD9ActiveQuotientClass period hPeriod packet) =
      enrichedD9ActiveEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction packet := by
  rw [quotientEuler_eq_activeEuler_equiv]
  simp [enrichedD9ActiveQuotientClass, enrichedD9ActiveEuler]

end
end P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ActiveQuotientBridge4D
end JanusFormal
