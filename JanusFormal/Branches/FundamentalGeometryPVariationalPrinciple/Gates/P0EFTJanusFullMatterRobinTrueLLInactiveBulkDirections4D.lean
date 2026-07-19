import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActualHessian4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveBulkDirections4D

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
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusMatterRobinFullLLActualHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Equality of exactly the directions read by the matter--Robin--LL sector. -/
def SameActiveDirections
    (first second : FullMatterRobinLLDirections period hPeriod) : Prop :=
  first.common.matter = second.common.matter ∧
  first.common.ll = second.common.ll ∧ first.robin = second.robin ∧
  first.llAuxMetric = second.llAuxMetric ∧ first.llMeasure = second.llMeasure

theorem fullMatterRobinTrueLLEuler_sameActive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (h : SameActiveDirections period hPeriod first second) :
    fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction first =
      fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction second := by
  rcases h with ⟨hMatter, hField, hRobin, hAux, hMeasure⟩
  have hLL : fullDirectionLLVariation period hPeriod first =
      fullDirectionLLVariation period hPeriod second := by
    unfold fullDirectionLLVariation
    rw [hMeasure, hField]
  unfold fullMatterRobinTrueLLEuler globalPTFullLLFirstVariation
  rw [hLL]
  simp only [hMatter, hField, hRobin, hAux]

theorem fullMatterRobinTrueLLAction_curve_sameActive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (h : SameActiveDirections period hPeriod first second) (t : Real) :
    globalMatterMultipletAction period hPeriod matterData
        (matterMultipletAffineCurve period hPeriod
          (independentMatterComponentFamily period hPeriod fields)
          (matterVariationComponentFamily period hPeriod first.common.matter) t) +
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction first.robin t) robinMeasure +
      globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFullCurve period hPeriod fields first.llAuxMetric
          first.llMeasure first.common.ll t) llMeasure =
    globalMatterMultipletAction period hPeriod matterData
        (matterMultipletAffineCurve period hPeriod
          (independentMatterComponentFamily period hPeriod fields)
          (matterVariationComponentFamily period hPeriod second.common.matter) t) +
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction second.robin t) robinMeasure +
      globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFullCurve period hPeriod fields second.llAuxMetric
          second.llMeasure second.common.ll t) llMeasure := by
  rcases h with ⟨hMatter, hField, hRobin, hAux, hMeasure⟩
  simp only [hMatter, hField, hRobin, hAux, hMeasure]

theorem globalMatterRobinFullLLHessian_sameActive_left
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first first' second : FullMatterRobinLLDirections period hPeriod)
    (h : SameActiveDirections period hPeriod first first') :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first' second := by
  rcases h with ⟨hMatter, hField, hRobin, hAux, hMeasure⟩
  have hLL : fullDirectionLLVariation period hPeriod first =
      fullDirectionLLVariation period hPeriod first' := by
    unfold fullDirectionLLVariation
    rw [hMeasure, hField]
  unfold globalMatterRobinFullLLHessian globalPTFullLLHessianForm
  rw [hLL]
  simp only [hMatter, hField, hRobin, hAux]

theorem globalMatterRobinFullLLHessian_sameActive_right
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second second' : FullMatterRobinLLDirections period hPeriod)
    (h : SameActiveDirections period hPeriod second second') :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second' := by
  rw [globalMatterRobinFullLLHessian_symmetric]
  rw [globalMatterRobinFullLLHessian_sameActive_left period hPeriod matterData
    kPlus kMinus robinMeasure frame llMeasure fields second second' first h]
  rw [globalMatterRobinFullLLHessian_symmetric]

end
end P0EFTJanusFullMatterRobinTrueLLInactiveBulkDirections4D
end JanusFormal
