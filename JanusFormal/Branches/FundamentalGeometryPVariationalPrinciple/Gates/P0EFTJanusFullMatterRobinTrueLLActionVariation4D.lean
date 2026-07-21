import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusTruePTFullLLFirstVariationBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActionVariation4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLActionVariation4D

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
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusTruePTFullLLFirstVariationBridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Exact existing matter action plus Robin action plus the true three-slot PT LL action. -/
def fullMatterRobinTrueLLAction
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) : Real :=
  globalMatterMultipletAction period hPeriod matterData
      (independentMatterComponentFamily period hPeriod fields) +
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus junction
      robinMeasure +
    globalPTSymmetricDifferentialLLAction period hPeriod frame fields llMeasure

/-- Common curve. Metric, gauge, ghost, and non-LL auxiliary directions are
retained by `direction.common` but are explicitly inactive in this action. -/
def fullMatterRobinTrueLLEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) : Real :=
  globalMatterMultipletEuler period hPeriod matterData
      (independentMatterComponentFamily period hPeriod fields)
      (matterVariationComponentFamily period hPeriod direction.common.matter) +
    robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus junction
      direction.robin robinMeasure +
    globalPTFullLLFirstVariation period hPeriod frame fields direction llMeasure

theorem fullMatterRobinTrueLLAction_hasDerivAt
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    HasDerivAt (fun t : Real =>
      globalMatterMultipletAction period hPeriod matterData
        (matterMultipletAffineCurve period hPeriod
          (independentMatterComponentFamily period hPeriod fields)
          (matterVariationComponentFamily period hPeriod direction.common.matter) t) +
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction direction.robin t) robinMeasure +
      globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
          direction.llMeasure direction.common.ll t) llMeasure)
      (fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction) 0 := by
  have hm := globalMatterMultipletAction_hasDerivAt period hPeriod matterData
    (independentMatterComponentFamily period hPeriod fields)
    (matterVariationComponentFamily period hPeriod direction.common.matter)
  have hr := robinJunctionAction_affine_hasDerivAt period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction direction.robin robinMeasure
  have hll := truePTAction_fullCurve_hasDerivAt_fullFirstVariation period hPeriod
    frame fields direction llMeasure
  unfold fullMatterRobinTrueLLEuler
  exact (hm.add hr).add hll

end
end P0EFTJanusFullMatterRobinTrueLLActionVariation4D
end JanusFormal
