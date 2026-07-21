import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinLLActualActionEulerHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLHessianVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterActionVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActionVariation4D

/-! Actual assembled matter, Robin, and full three-slot LL Hessian. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLActualHessian4D

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
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D

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

/-- First variation of the three actual sector actions on the faithful full
direction packet. -/
def globalMatterRobinFullLLFirstVariation
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) : Real :=
  (globalMatterMultipletEuler period hPeriod matterData matter
      (matterVariationComponentFamily period hPeriod direction.common.matter) +
    robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus junction
      direction.robin robinMeasure) +
    globalPTFullLLFirstVariation period hPeriod frame llFields direction llMeasure

/-- Sum of the genuine matter, Robin, and full LL Hessians. -/
def globalMatterRobinFullLLHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (llFields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) : Real :=
  (globalMatterMultipletHessian period hPeriod matterData
      (matterVariationComponentFamily period hPeriod first.common.matter)
      (matterVariationComponentFamily period hPeriod second.common.matter) +
    robinHessian period hPeriod kPlus kMinus first.robin second.robin robinMeasure) +
    globalPTFullLLHessianForm period hPeriod frame llFields first second llMeasure

/-- On the actual common field configuration this is exactly the Euler
functional of `fullMatterRobinTrueLLAction`, not a parallel model. -/
theorem globalMatterRobinFullLLFirstVariation_eq_trueActionEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLFirstVariation period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure
        (independentMatterComponentFamily period hPeriod fields) junction fields direction =
      fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction := by
  rfl

theorem globalMatterRobinFullLLHessian_symmetric
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (llFields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure llFields first second =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure llFields second first := by
  unfold globalMatterRobinFullLLHessian
  rw [globalMatterMultipletHessian_symmetric,
    robinHessian_symmetric, globalPTFullLLHessianForm_symmetric]

/-- Differentiating the actual assembled first variation along the second
full direction gives the assembled Hessian. -/
theorem globalMatterRobinFullLLFirstVariation_second_direction_hasDerivAt
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    HasDerivAt
      (fun t : Real => globalMatterRobinFullLLFirstVariation period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        (matterMultipletAffineCurve period hPeriod matter
          (matterVariationComponentFamily period hPeriod second.common.matter) t)
        (junctionAffineCurve period hPeriod junction second.robin t)
        (fullLLCurve period hPeriod llFields
          (fullDirectionLLVariation period hPeriod second) second.llAuxMetric t)
        first)
      (globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure llFields first second) 0 := by
  have hM := globalMatterMultipletEuler_hasDerivAt period hPeriod matterData matter
    (matterVariationComponentFamily period hPeriod second.common.matter)
    (matterVariationComponentFamily period hPeriod first.common.matter)
  have hR := robinWeakBalance_linearized_hasDerivAt period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction second.robin first.robin robinMeasure
  have hM' : HasDerivAt
      (fun epsilon : Real => globalMatterMultipletEuler period hPeriod matterData
        (matterMultipletAffineCurve period hPeriod matter
          (matterVariationComponentFamily period hPeriod second.common.matter) epsilon)
        (matterVariationComponentFamily period hPeriod first.common.matter))
      (globalMatterMultipletHessian period hPeriod matterData
        (matterVariationComponentFamily period hPeriod first.common.matter)
        (matterVariationComponentFamily period hPeriod second.common.matter)) 0 := by
    rw [globalMatterMultipletHessian_symmetric]
    exact hM
  have hR' : HasDerivAt
      (fun epsilon : Real =>
        (robinWeakBalanceOperator period hPeriod kPlus kMinus bulkPlus bulkMinus
          (junctionAffineCurve period hPeriod junction second.robin epsilon)
          robinMeasure) first.robin)
      (robinHessian period hPeriod kPlus kMinus first.robin second.robin robinMeasure) 0 := by
    rw [robinHessian_symmetric]
    exact hR
  have hLLRaw := globalPTFullLLFirstVariation_second_direction_hasDerivAt
    period hPeriod frame llFields first second llMeasure
  have hLL : HasDerivAt
      (fun t : Real => globalPTFullLLFirstVariation period hPeriod frame
        (fullLLCurve period hPeriod llFields
          (fullDirectionLLVariation period hPeriod second) second.llAuxMetric t)
        first llMeasure)
      (globalPTFullLLHessianForm period hPeriod frame llFields first second llMeasure) 0 := by
    rw [show (fun t : Real => globalPTFullLLFirstVariation period hPeriod frame
        (fullLLCurve period hPeriod llFields
          (fullDirectionLLVariation period hPeriod second) second.llAuxMetric t)
        first llMeasure) =
      ((fun t : Real => ∫ p,
        P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D.ptSymmetricDifferentialLLKineticFirstVariation
          period hPeriod frame (llFields.llAuxMetric + t • second.llAuxMetric)
          (llFields.llField + t • second.common.ll)
          first.llAuxMetric first.common.ll p ∂llMeasure) +
       (fun t : Real =>
        P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D.globalPTLLFirstVariation
          period hPeriod
          (llMeasureFieldCurve period hPeriod llFields
            (fullDirectionLLVariation period hPeriod second) t t)
          (fullDirectionLLVariation period hPeriod first) llMeasure)) by
      funext t
      unfold globalPTFullLLFirstVariation fullLLCurve fullDirectionLLVariation
        llMeasureFieldCurve
        P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D.globalPTLLFirstVariation
        P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D.ptLLFirstVariationDensity
        llFirstVariationDensity
      rfl]
    exact hLLRaw
  have h := (hM'.add hR').add hLL
  unfold globalMatterRobinFullLLFirstVariation globalMatterRobinFullLLHessian
  change HasDerivAt
    (((fun epsilon : Real => globalMatterMultipletEuler period hPeriod matterData
        (matterMultipletAffineCurve period hPeriod matter
          (matterVariationComponentFamily period hPeriod second.common.matter) epsilon)
        (matterVariationComponentFamily period hPeriod first.common.matter)) +
      (fun epsilon : Real => robinFirstVariation period hPeriod kPlus kMinus
        bulkPlus bulkMinus (junctionAffineCurve period hPeriod junction second.robin epsilon)
        first.robin robinMeasure)) +
      (fun t : Real => globalPTFullLLFirstVariation period hPeriod frame
        (fullLLCurve period hPeriod llFields
          (fullDirectionLLVariation period hPeriod second) second.llAuxMetric t)
        first llMeasure)) _ 0
  simpa [robinWeakBalanceOperator] using h

end
end P0EFTJanusMatterRobinFullLLActualHessian4D
end JanusFormal
