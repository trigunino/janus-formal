import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActionVariation4D

/-!
# Active projection of enriched matter + Robin + LL directions

The existing assembled action only sees the matter, Robin, and LL entries of
an enriched common direction.  This gate records that exact factorization; it
does not concern the absent Candidate-A sectors.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLActiveProjection4D

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
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusMatterRobinLLActualActionEulerHessian4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D

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

/-- Exactly the three direction entries seen by the assembled action. -/
@[ext]
structure ActiveMatterRobinLLDirection where
  matter : SmoothQuotientField period hPeriod MatterFiber ×
    SmoothQuotientField period hPeriod MatterFiber
  robin : SmoothThroatField period hPeriod Real
  ll : SmoothThroatField period hPeriod LLFieldFiber

def activeMatterRobinLLProjection
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    ActiveMatterRobinLLDirection period hPeriod where
  matter := direction.common.matter
  robin := direction.robin
  ll := direction.common.ll

/-- Euler pairing factored through the active projection. -/
def activeMatterRobinLLEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ActiveMatterRobinLLDirection period hPeriod) : Real :=
  matterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure
    (independentMatterComponentFamily period hPeriod fields)
    (matterVariationComponentFamily period hPeriod direction.matter)
    junction direction.robin fields direction.ll

theorem commonMatterRobinLLEuler_factors_activeProjection
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction =
      activeMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction
        (activeMatterRobinLLProjection period hPeriod direction) :=
  rfl

/-- Hessian pairing factored through the active projections of both slots. -/
def activeMatterRobinLLHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : ActiveMatterRobinLLDirection period hPeriod) : Real :=
  matterRobinLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
    llMeasure
    (matterVariationComponentFamily period hPeriod first.matter)
    (matterVariationComponentFamily period hPeriod second.matter)
    first.robin second.robin fields first.ll second.ll

theorem commonMatterRobinLLHessian_factors_activeProjection
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : MatterRobinLLEnrichedDirections period hPeriod) :
    commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      activeMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields
        (activeMatterRobinLLProjection period hPeriod first)
        (activeMatterRobinLLProjection period hPeriod second) :=
  rfl

theorem commonMatterRobinLLEuler_congr_activeProjection
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (first second : MatterRobinLLEnrichedDirections period hPeriod)
    (hActive : activeMatterRobinLLProjection period hPeriod first =
      activeMatterRobinLLProjection period hPeriod second) :
    commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction first =
      commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction second := by
  rw [commonMatterRobinLLEuler_factors_activeProjection,
    commonMatterRobinLLEuler_factors_activeProjection, hActive]

theorem commonMatterRobinLLHessian_congr_left_activeProjection
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first first' second : MatterRobinLLEnrichedDirections period hPeriod)
    (hActive : activeMatterRobinLLProjection period hPeriod first =
      activeMatterRobinLLProjection period hPeriod first') :
    commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first' second := by
  rw [commonMatterRobinLLHessian_factors_activeProjection,
    commonMatterRobinLLHessian_factors_activeProjection, hActive]

theorem commonMatterRobinLLHessian_congr_right_activeProjection
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second second' : MatterRobinLLEnrichedDirections period hPeriod)
    (hActive : activeMatterRobinLLProjection period hPeriod second =
      activeMatterRobinLLProjection period hPeriod second') :
    commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second' := by
  rw [commonMatterRobinLLHessian_factors_activeProjection,
    commonMatterRobinLLHessian_factors_activeProjection, hActive]

end

end P0EFTJanusCommonMatterRobinLLActiveProjection4D
end JanusFormal
