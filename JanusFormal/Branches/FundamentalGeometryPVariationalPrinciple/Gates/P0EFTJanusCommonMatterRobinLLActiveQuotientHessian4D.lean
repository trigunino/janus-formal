import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActionReconstruction4D

/-!
# Active-direction quotient of the matter--Robin--LL Hessian

The quotient forgets precisely the metric, gauge, ghost and auxiliary
directions ignored by this sectorial action.  It is not a quotient for the
complete Candidate-A action.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLActiveQuotientHessian4D

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
open P0EFTJanusCommonMatterRobinLLActionVariation4D
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

/-- The three directions actually consumed by the sectorial action. -/
structure ActiveMatterRobinLLDirection where
  matter : MatterComponentFamily period hPeriod
  robin : SmoothThroatField period hPeriod Real
  ll : SmoothThroatField period hPeriod LLFieldFiber

def activeDirection
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    ActiveMatterRobinLLDirection period hPeriod where
  matter := matterVariationComponentFamily period hPeriod direction.common.matter
  robin := direction.robin
  ll := direction.common.ll

/-- Two enriched directions are equivalent when this action sees identical
matter, Robin and LL directions. -/
def activeDirectionSetoid :
    Setoid (MatterRobinLLEnrichedDirections period hPeriod) where
  r first second :=
    activeDirection period hPeriod first = activeDirection period hPeriod second
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

abbrev ActiveMatterRobinLLQuotient :=
  Quotient (activeDirectionSetoid period hPeriod)

theorem commonMatterRobinLLHessian_congr_active
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    {first first' second second' :
      MatterRobinLLEnrichedDirections period hPeriod}
    (hFirst : activeDirection period hPeriod first =
      activeDirection period hPeriod first')
    (hSecond : activeDirection period hPeriod second =
      activeDirection period hPeriod second') :
    commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first' second' := by
  have hMatterFirst := congrArg ActiveMatterRobinLLDirection.matter hFirst
  have hRobinFirst := congrArg ActiveMatterRobinLLDirection.robin hFirst
  have hLLFirst := congrArg ActiveMatterRobinLLDirection.ll hFirst
  have hMatterSecond := congrArg ActiveMatterRobinLLDirection.matter hSecond
  have hRobinSecond := congrArg ActiveMatterRobinLLDirection.robin hSecond
  have hLLSecond := congrArg ActiveMatterRobinLLDirection.ll hSecond
  change matterVariationComponentFamily period hPeriod first.common.matter =
    matterVariationComponentFamily period hPeriod first'.common.matter at hMatterFirst
  change first.robin = first'.robin at hRobinFirst
  change first.common.ll = first'.common.ll at hLLFirst
  change matterVariationComponentFamily period hPeriod second.common.matter =
    matterVariationComponentFamily period hPeriod second'.common.matter at hMatterSecond
  change second.robin = second'.robin at hRobinSecond
  change second.common.ll = second'.common.ll at hLLSecond
  unfold commonMatterRobinLLHessian
  rw [hMatterFirst, hRobinFirst, hLLFirst, hMatterSecond, hRobinSecond,
    hLLSecond]

/-- Hessian of the unchanged sectorial action descended to active classes. -/
def quotientMatterRobinLLHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : ActiveMatterRobinLLQuotient period hPeriod) : Real :=
  Quotient.liftOn₂ first second
    (commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields)
    (by
      intro first second first' second' hFirst hSecond
      exact commonMatterRobinLLHessian_congr_active period hPeriod matterData
        kPlus kMinus robinMeasure frame llMeasure fields hFirst hSecond)

@[simp]
theorem quotientMatterRobinLLHessian_mk
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : MatterRobinLLEnrichedDirections period hPeriod) :
    quotientMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields
        (Quotient.mk (activeDirectionSetoid period hPeriod) first)
        (Quotient.mk (activeDirectionSetoid period hPeriod) second) =
      commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second :=
  rfl

theorem quotientMatterRobinLLHessian_symmetric
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : ActiveMatterRobinLLQuotient period hPeriod) :
    quotientMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      quotientMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields second first := by
  induction first using Quotient.inductionOn with
  | _ first =>
      induction second using Quotient.inductionOn with
      | _ second =>
          exact matterRobinLLHessian_symmetric period hPeriod matterData kPlus
            kMinus robinMeasure frame llMeasure
            (matterVariationComponentFamily period hPeriod first.common.matter)
            (matterVariationComponentFamily period hPeriod second.common.matter)
            first.robin second.robin fields first.common.ll second.common.ll

end

end P0EFTJanusCommonMatterRobinLLActiveQuotientHessian4D
end JanusFormal
