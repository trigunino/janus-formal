import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActiveQuotientHessian4D

/-!
# Euler pairing on the active matter--Robin--LL quotient

The Euler pairing of the existing sectorial action descends in its test
direction.  Its genuine representative-level linearization has the already
descended quotient Hessian as derivative.  No differentiable structure on the
set quotient and no complete Candidate-A action are asserted.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLQuotientEulerVariation4D

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
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusMatterRobinLLActualActionEulerHessian4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusCommonMatterRobinLLActiveQuotientHessian4D

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

theorem commonMatterRobinLLEuler_congr_active
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    {first second : MatterRobinLLEnrichedDirections period hPeriod}
    (hActive : activeDirection period hPeriod first =
      activeDirection period hPeriod second) :
    commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction first =
      commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction second := by
  have hMatter := congrArg ActiveMatterRobinLLDirection.matter hActive
  have hRobin := congrArg ActiveMatterRobinLLDirection.robin hActive
  have hLL := congrArg ActiveMatterRobinLLDirection.ll hActive
  change matterVariationComponentFamily period hPeriod first.common.matter =
    matterVariationComponentFamily period hPeriod second.common.matter at hMatter
  change first.robin = second.robin at hRobin
  change first.common.ll = second.common.ll at hLL
  unfold commonMatterRobinLLEuler
  rw [hMatter, hRobin, hLL]

/-- Common Euler pairing descended to the active test-direction quotient. -/
def quotientMatterRobinLLEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ActiveMatterRobinLLQuotient period hPeriod) : Real :=
  Quotient.liftOn direction
    (commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure fields junction)
    (fun _ _ hActive => commonMatterRobinLLEuler_congr_active period hPeriod
      matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
      fields junction hActive)

@[simp]
theorem quotientMatterRobinLLEuler_mk
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    quotientMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction
        (Quotient.mk (activeDirectionSetoid period hPeriod) direction) =
      commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction :=
  rfl

/-- Genuine Euler linearization on representatives, with derivative expressed
by the effective quotient Hessian. -/
theorem commonMatterRobinLLEuler_hasDerivAt_quotientHessian_mk
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
    (first second : MatterRobinLLEnrichedDirections period hPeriod) :
    HasDerivAt
      (fun epsilon : Real => matterRobinLLEuler period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        (matterMultipletAffineCurve period hPeriod
          (independentMatterComponentFamily period hPeriod fields)
          (matterVariationComponentFamily period hPeriod first.common.matter)
          epsilon)
        (matterVariationComponentFamily period hPeriod second.common.matter)
        (junctionAffineCurve period hPeriod junction first.robin epsilon)
        second.robin
        (differentialLLFluxCurve period hPeriod fields first.common.ll epsilon)
        second.common.ll)
      (quotientMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields
        (Quotient.mk (activeDirectionSetoid period hPeriod) first)
        (Quotient.mk (activeDirectionSetoid period hPeriod) second)) 0 := by
  rw [quotientMatterRobinLLHessian_mk]
  exact commonMatterRobinLLEuler_hasDerivAt period hPeriod matterData kPlus
    kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    first second

end

end P0EFTJanusCommonMatterRobinLLQuotientEulerVariation4D
end JanusFormal
