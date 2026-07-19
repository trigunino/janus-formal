import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLExactTaylor4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D

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
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusFullMatterRobinTrueLLExactTaylor4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- The assembled action evaluated on the synchronized matter, Robin, and
three-slot LL curve. -/
def fullMatterRobinTrueLLCurve
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) (t : Real) : Real :=
  globalMatterMultipletAction period hPeriod matterData
      (matterMultipletAffineCurve period hPeriod
        (independentMatterComponentFamily period hPeriod fields)
        (matterVariationComponentFamily period hPeriod direction.common.matter) t) +
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
      (junctionAffineCurve period hPeriod junction direction.robin t) robinMeasure +
    globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
        direction.llMeasure direction.common.ll t) llMeasure

private theorem assembled_curve_polynomial
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus
      kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      direction t) = fun t =>
      fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus
          bulkMinus robinMeasure frame llMeasure fields junction +
        t * fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus
          bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction +
        (t ^ 2 / 2) * globalMatterRobinFullLLHessian period hPeriod matterData
          kPlus kMinus robinMeasure frame llMeasure fields direction direction +
        t ^ 3 * globalPTFullLLTaylorCubic period hPeriod frame fields
          direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction)
          llMeasure +
        t ^ 4 * globalPTFullLLTaylorQuartic period hPeriod frame fields
          direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction)
          llMeasure := by
  funext t
  exact fullMatterRobinTrueLLAction_exact_taylor period hPeriod matterData kPlus
    kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t

theorem fullMatterRobinTrueLLCurve_third_iteratedDeriv
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    iteratedDeriv 3 (fun t => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      direction t) 0 =
      6 * globalPTFullLLTaylorCubic period hPeriod frame fields
        direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction)
        llMeasure := by
  rw [assembled_curve_polynomial period hPeriod matterData kPlus kMinus bulkPlus
    bulkMinus robinMeasure frame llMeasure fields junction direction]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_mul,
    iteratedDeriv_const, iteratedDeriv_fun_id_zero, iteratedDeriv_fun_pow_zero]
  norm_num [Finset.sum_range_succ]

theorem fullMatterRobinTrueLLCurve_fourth_iteratedDeriv
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    iteratedDeriv 4 (fun t => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      direction t) 0 =
      24 * globalPTFullLLTaylorQuartic period hPeriod frame fields
        direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction)
        llMeasure := by
  rw [assembled_curve_polynomial period hPeriod matterData kPlus kMinus bulkPlus
    bulkMinus robinMeasure frame llMeasure fields junction direction]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_mul,
    iteratedDeriv_const, iteratedDeriv_fun_id_zero, iteratedDeriv_fun_pow_zero]
  norm_num [Finset.sum_range_succ]

end
end P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
end JanusFormal
