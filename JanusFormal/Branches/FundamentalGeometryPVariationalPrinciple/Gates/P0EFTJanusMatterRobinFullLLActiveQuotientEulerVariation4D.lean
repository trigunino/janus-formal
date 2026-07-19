import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D

/-! Euler descent and representative variation on the active quotient. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D

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
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- The true Euler functional descended to the explicit active quotient. -/
def quotientEuler
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) :
    ActiveQuotient period hPeriod → Real :=
  Quotient.lift
    (fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure fields junction)
    (by
      intro first second h
      rw [trueEuler_factors_active, trueEuler_factors_active, h])

theorem quotientEuler_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    quotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction ⟦direction⟧ =
      fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction := by
  rfl

/-- Representative Euler curve used by the already proved actual Hessian variation. -/
def representativeEulerCurve
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) (t : Real) : Real :=
  globalMatterRobinFullLLFirstVariation period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure
    (matterMultipletAffineCurve period hPeriod matter
      (matterVariationComponentFamily period hPeriod second.common.matter) t)
    (junctionAffineCurve period hPeriod junction second.robin t)
    (fullLLCurve period hPeriod fields
      (fullDirectionLLVariation period hPeriod second) second.llAuxMetric t) first

theorem representativeEulerCurve_hasDerivAt_quotientHessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first second)
      (quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields ⟦first⟧ ⟦second⟧) 0 := by
  rw [quotientHessian_mk]
  unfold representativeEulerCurve
  exact globalMatterRobinFullLLFirstVariation_second_direction_hasDerivAt
    period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
      llMeasure matter junction fields first second

theorem quotientHessian_symmetric
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first second =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields second first := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      rw [quotientHessian_mk, quotientHessian_mk]
      exact globalMatterRobinFullLLHessian_symmetric
        period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second

end
end P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
end JanusFormal
