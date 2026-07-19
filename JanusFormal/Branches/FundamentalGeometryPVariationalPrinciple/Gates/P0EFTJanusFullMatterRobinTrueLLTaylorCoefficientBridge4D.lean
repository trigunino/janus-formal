import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLExactTaylor4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusMatterRobinFullLLActualHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Integrated linear coefficient obtained by summing the three sector Taylor
coefficients before identifying it with the assembled Euler functional. -/
def fullMatterRobinTrueLLTaylorC1
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
    globalPTFullLLTaylorEuler period hPeriod frame fields direction.llAuxMetric
      (fullDirectionLLVariation period hPeriod direction) llMeasure

/-- Integrated quadratic coefficient obtained sectorwise, including the
normalizing halves on the genuine matter, Robin, and LL Hessians. -/
def fullMatterRobinTrueLLTaylorC2
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) : Real :=
  (1 / 2 : Real) * globalMatterMultipletHessian period hPeriod matterData
      (matterVariationComponentFamily period hPeriod direction.common.matter)
      (matterVariationComponentFamily period hPeriod direction.common.matter) +
    (1 / 2 : Real) * robinHessian period hPeriod kPlus kMinus direction.robin
      direction.robin robinMeasure +
    (1 / 2 : Real) * globalPTFullLLTaylorHessianDiagonal period hPeriod frame
      fields direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction)
      llMeasure

theorem fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction =
      fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction := by
  unfold fullMatterRobinTrueLLTaylorC1
  rw [globalPTFullLLTaylorEuler_eq_actual period hPeriod frame fields direction
    llMeasure]
  unfold fullMatterRobinTrueLLEuler fullLLEuler globalPTFullLLFirstVariation
  rfl

theorem fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields direction =
      (1 / 2 : Real) * globalMatterRobinFullLLHessian period hPeriod matterData
        kPlus kMinus robinMeasure frame llMeasure fields direction direction := by
  unfold fullMatterRobinTrueLLTaylorC2
  rw [globalPTFullLLTaylorHessianDiagonal_eq_actual period hPeriod frame fields
    direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction)
    llMeasure]
  unfold globalMatterRobinFullLLHessian
  simp only [fullDirectionLLVariation, globalPTFullLLHessianForm]
  ring

end
end P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
end JanusFormal
