import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActionVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinLLActionReconstruction4D

/-!
# Reconstruction on the enriched matter--Robin--LL packet

This is the same assembled action and the same enriched variation packet.
The Robin value at the zero junction is retained as an explicit normalization
constant.  No Candidate-A action is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLActionReconstruction4D

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
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusMatterRobinLLActualActionEulerHessian4D
open P0EFTJanusMatterRobinLLActionReconstruction4D

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

/-- Radial enriched direction from the reference packet to the supplied
matter, junction and LL variables. -/
def matterRobinLLRadialDirection
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) :
    MatterRobinLLEnrichedDirections period hPeriod where
  common := {
    metric := zeroSmoothDiagonalMetricVariation period hPeriod
    matter := fields.matter
    gauge := 0
    ghost := 0
    auxiliary := 0
    ll := fields.llField }
  robin := junction

/-- Exact reconstruction on the enriched common packet.  The first term is
the retained normalization constant, the second is the affine Robin Euler
term at the zero junction, and the last is half the actual enriched Hessian. -/
theorem commonMatterRobinLLAction_reconstructed
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) :
    matterRobinLLAction period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure
        (independentMatterComponentFamily period hPeriod fields) junction fields =
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
          0 robinMeasure +
        robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          0 junction robinMeasure +
        (1 / 2 : Real) *
          commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
            robinMeasure frame llMeasure fields
            (matterRobinLLRadialDirection period hPeriod fields junction)
            (matterRobinLLRadialDirection period hPeriod fields junction) := by
  change matterRobinLLAction period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure
      (independentMatterComponentFamily period hPeriod fields) junction fields =
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus 0
        robinMeasure +
      robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus 0
        junction robinMeasure +
      (1 / 2 : Real) * matterRobinLLHessian period hPeriod matterData kPlus
        kMinus robinMeasure frame llMeasure
        (independentMatterComponentFamily period hPeriod fields)
        (independentMatterComponentFamily period hPeriod fields)
        junction junction fields fields.llField fields.llField
  exact matterRobinLLAction_reconstructed_from_euler_and_hessian period hPeriod
    matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
    (independentMatterComponentFamily period hPeriod fields) junction fields

end

end P0EFTJanusCommonMatterRobinLLActionReconstruction4D
end JanusFormal
