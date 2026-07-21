import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinLLActualActionEulerHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalMatterMultipletActionReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRobinJunctionActionReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLActionReconstruction4D

namespace JanusFormal
namespace P0EFTJanusMatterRobinLLActionReconstruction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
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
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusGlobalMatterMultipletActionReconstruction4D
open P0EFTJanusRobinJunctionActionReconstruction4D
open P0EFTJanusDifferentialLLActionReconstruction4D
open P0EFTJanusMatterRobinLLActualActionEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Exact affine-quadratic reconstruction of the action containing all eight
matter coordinates, Robin, and LL. -/
theorem matterRobinLLAction_reconstructed_from_euler_and_hessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod) :
    matterRobinLLAction period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure matter junction llFields =
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
          (0 : SmoothThroatField period hPeriod Real) robinMeasure +
        robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          (0 : SmoothThroatField period hPeriod Real) junction robinMeasure +
        (1 / 2 : Real) *
          matterRobinLLHessian period hPeriod matterData kPlus kMinus
            robinMeasure frame llMeasure matter matter junction junction
            llFields llFields.llField llFields.llField := by
  unfold matterRobinLLAction matterRobinLLHessian
  rw [globalMatterMultipletAction_eq_half_hessian period hPeriod matterData
    matter]
  rw [robinJunctionAction_reconstructed_from_euler_and_actualHessian period
    hPeriod kPlus kMinus bulkPlus bulkMinus junction junction robinMeasure]
  rw [robinJunctionActionMixedHessian_eq_robinHessian period hPeriod kPlus
    kMinus bulkPlus bulkMinus junction junction junction robinMeasure]
  rw [globalPTSymmetricDifferentialLLAction_eq_half_fluxHessian period hPeriod
    frame llFields llMeasure]
  ring

end

end P0EFTJanusMatterRobinLLActionReconstruction4D
end JanusFormal
