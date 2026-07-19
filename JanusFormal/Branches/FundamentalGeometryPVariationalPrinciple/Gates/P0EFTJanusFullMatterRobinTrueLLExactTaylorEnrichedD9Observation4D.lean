import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLExactTaylor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorC1EnrichedD9Observation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorC2EnrichedD9Observation4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLExactTaylorEnrichedD9Observation4D

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
open P0EFTJanusFullMatterRobinTrueLLExactTaylor4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Euler4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Exact Taylor formula for the true assembled action. The enriched D9
observation supplies precisely the active Euler and diagonal Hessian readings;
the genuinely nonlinear cubic and quartic LL coefficients remain explicit. -/
theorem fullMatterRobinTrueLLAction_exact_taylor_enrichedD9
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
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) (t : Real) :
    globalMatterMultipletAction period hPeriod matterData
        (matterMultipletAffineCurve period hPeriod
          (independentMatterComponentFamily period hPeriod fields)
          (matterVariationComponentFamily period hPeriod direction.common.matter) t) +
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction direction.robin t) robinMeasure +
      globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
          direction.llMeasure direction.common.ll t) llMeasure =
      fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus
          bulkMinus robinMeasure frame llMeasure fields junction +
        t * enrichedD9ActiveEuler period hPeriod matterData kPlus kMinus bulkPlus
          bulkMinus robinMeasure frame llMeasure fields junction
          (globalMatterEnrichedD9Projection period hPeriod fields direction sector
            column point) +
        (t ^ 2 / 2) * enrichedD9ActiveHessian period hPeriod matterData kPlus
          kMinus robinMeasure frame llMeasure fields
          (globalMatterEnrichedD9Projection period hPeriod fields direction sector
            column point)
          (globalMatterEnrichedD9Projection period hPeriod fields direction sector
            column point) +
        t ^ 3 * globalPTFullLLTaylorCubic period hPeriod frame fields
          direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction)
          llMeasure +
        t ^ 4 * globalPTFullLLTaylorQuartic period hPeriod frame fields
          direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction)
          llMeasure := by
  rw [fullMatterRobinTrueLLAction_exact_taylor period hPeriod matterData kPlus
      kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      direction t,
    trueEuler_eq_enrichedD9ActiveEuler,
    fullHessian_eq_enrichedD9ActiveHessian]

end
end P0EFTJanusFullMatterRobinTrueLLExactTaylorEnrichedD9Observation4D
end JanusFormal
