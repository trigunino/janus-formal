import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLExactTaylor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEulerReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientKernelReconstruction4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLExactTaylorActiveQuotient4D

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
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusGlobalMatterMultipletAffineTaylor4D
open P0EFTJanusRobinJunctionActionReconstruction4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLExactTaylor4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D

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

/-- Exact assembled Taylor identity with its linear and quadratic terms evaluated
on the active quotient class recovered through `activeQuotientEquiv`.  The LL
cubic and quartic coefficients remain the explicit representative coefficients;
no curve or additive structure on the quotient is introduced. -/
theorem fullMatterRobinTrueLLAction_exact_taylor_activeQuotient
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
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
        t * quotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
          robinMeasure frame llMeasure fields junction
          ((activeQuotientEquiv period hPeriod).symm
            (activeProjection period hPeriod direction)) +
        (t ^ 2 / 2) * quotientHessian period hPeriod matterData kPlus kMinus
          robinMeasure frame llMeasure fields
          ((activeQuotientEquiv period hPeriod).symm
            (activeProjection period hPeriod direction))
          ((activeQuotientEquiv period hPeriod).symm
            (activeProjection period hPeriod direction)) +
        t ^ 3 * globalPTFullLLTaylorCubic period hPeriod frame fields
          direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction)
          llMeasure +
        t ^ 4 * globalPTFullLLTaylorQuartic period hPeriod frame fields
          direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction)
          llMeasure := by
  have hclass :
      (activeQuotientEquiv period hPeriod).symm
          (activeProjection period hPeriod direction) =
        (⟦direction⟧ : ActiveQuotient period hPeriod) := by
    apply (activeQuotientEquiv period hPeriod).injective
    simp
  rw [hclass, quotientEuler_mk, quotientHessian_mk]
  exact fullMatterRobinTrueLLAction_exact_taylor period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t

end
end P0EFTJanusFullMatterRobinTrueLLExactTaylorActiveQuotient4D
end JanusFormal
