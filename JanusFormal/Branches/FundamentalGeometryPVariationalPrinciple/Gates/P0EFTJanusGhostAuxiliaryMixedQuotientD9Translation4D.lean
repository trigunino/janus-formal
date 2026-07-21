import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGhostAuxiliaryMixedTranslationInvariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedEnrichedD9Observation4D

namespace JanusFormal
namespace P0EFTJanusGhostAuxiliaryMixedQuotientD9Translation4D
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
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9HessianCongruence4D
open P0EFTJanusGhostAuxiliaryTranslationInvariance4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

variable (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
  (robinMeasure : Measure (EffectiveThroat period hPeriod))
  (frame : SmoothThroatGeneratingFrame period hPeriod)
  (llMeasure : Measure (EffectiveThroat period hPeriod))
  (fields : IndependentFields period hPeriod)
  (first second : FullMatterRobinLLDirections period hPeriod)

theorem quotient_addGhost_first (ghost) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦addGhost period hPeriod first ghost⟧ ⟦second⟧ =
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦first⟧ ⟦second⟧ := by rw [addGhost_quotient]

theorem quotient_addGhost_second (ghost) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦first⟧ ⟦addGhost period hPeriod second ghost⟧ =
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦first⟧ ⟦second⟧ := by rw [addGhost_quotient]

theorem quotient_addGhost_both (ghostFirst ghostSecond) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦addGhost period hPeriod first ghostFirst⟧ ⟦addGhost period hPeriod second ghostSecond⟧ =
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦first⟧ ⟦second⟧ := by rw [addGhost_quotient, addGhost_quotient]

theorem quotient_addAuxiliary_first (auxiliary) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦addAuxiliary period hPeriod first auxiliary⟧ ⟦second⟧ =
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦first⟧ ⟦second⟧ := by rw [addAuxiliary_quotient]

theorem quotient_addAuxiliary_second (auxiliary) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦first⟧ ⟦addAuxiliary period hPeriod second auxiliary⟧ =
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦first⟧ ⟦second⟧ := by rw [addAuxiliary_quotient]

theorem quotient_addAuxiliary_both (auxiliaryFirst auxiliarySecond) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦addAuxiliary period hPeriod first auxiliaryFirst⟧
      ⟦addAuxiliary period hPeriod second auxiliarySecond⟧ =
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦first⟧ ⟦second⟧ := by rw [addAuxiliary_quotient, addAuxiliary_quotient]

variable (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)

private theorem d9_congr (first' second' : FullMatterRobinLLDirections period hPeriod)
    (hFirst : toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod
      fields first' sector column point) = toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point))
    (hSecond : toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod
      fields second' sector column point) = toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point)) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields first' sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields second' sector column point) =
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := by
  rw [enrichedD9ActiveHessian_congr_left period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields _ _ _ hFirst,
    enrichedD9ActiveHessian_congr_right period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields _ _ _ hSecond]

theorem d9_addGhost_first (ghost) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields (addGhost period hPeriod first ghost) sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) =
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := d9_congr period hPeriod matterData kPlus kMinus robinMeasure
  frame llMeasure fields first second sector column point (addGhost period hPeriod first ghost) second
  (addGhost_D9 period hPeriod fields sector column point first ghost) rfl

theorem d9_addGhost_second (ghost) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields (addGhost period hPeriod second ghost) sector column point) =
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := d9_congr period hPeriod matterData kPlus kMinus robinMeasure
  frame llMeasure fields first second sector column point first (addGhost period hPeriod second ghost)
  rfl (addGhost_D9 period hPeriod fields sector column point second ghost)

theorem d9_addGhost_both (ghostFirst ghostSecond) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields (addGhost period hPeriod first ghostFirst) sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields (addGhost period hPeriod second ghostSecond) sector column point) =
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := d9_congr period hPeriod matterData kPlus kMinus
  robinMeasure frame llMeasure fields first second sector column point
  (addGhost period hPeriod first ghostFirst) (addGhost period hPeriod second ghostSecond)
  (addGhost_D9 period hPeriod fields sector column point first ghostFirst)
  (addGhost_D9 period hPeriod fields sector column point second ghostSecond)

theorem d9_addAuxiliary_first (auxiliary) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields (addAuxiliary period hPeriod first auxiliary) sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) =
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := d9_congr period hPeriod matterData kPlus kMinus
  robinMeasure frame llMeasure fields first second sector column point
  (addAuxiliary period hPeriod first auxiliary) second
  (addAuxiliary_D9 period hPeriod fields sector column point first auxiliary) rfl

theorem d9_addAuxiliary_second (auxiliary) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields (addAuxiliary period hPeriod second auxiliary) sector column point) =
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := d9_congr period hPeriod matterData kPlus kMinus
  robinMeasure frame llMeasure fields first second sector column point first
  (addAuxiliary period hPeriod second auxiliary) rfl
  (addAuxiliary_D9 period hPeriod fields sector column point second auxiliary)

theorem d9_addAuxiliary_both (auxiliaryFirst auxiliarySecond) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields (addAuxiliary period hPeriod first auxiliaryFirst) sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields (addAuxiliary period hPeriod second auxiliarySecond) sector column point) =
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
      (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := d9_congr period hPeriod matterData
  kPlus kMinus robinMeasure frame llMeasure fields first second sector column point
  (addAuxiliary period hPeriod first auxiliaryFirst)
  (addAuxiliary period hPeriod second auxiliarySecond)
  (addAuxiliary_D9 period hPeriod fields sector column point first auxiliaryFirst)
  (addAuxiliary_D9 period hPeriod fields sector column point second auxiliarySecond)

end
end P0EFTJanusGhostAuxiliaryMixedQuotientD9Translation4D
end JanusFormal
