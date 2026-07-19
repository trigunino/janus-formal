import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveQuotientD9Kernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorC2EnrichedD9Observation4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveDiagonalOrderTwo4D

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
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
open P0EFTJanusFullMatterRobinTrueLLInactiveQuotientD9Kernel4D
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

theorem fullMatterRobinTrueLLTaylorC2_eq_zero_of_inactive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields direction = 0 := by
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    globalMatterRobinFullLLHessian_inactive_left period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields direction direction hInactive, mul_zero]

theorem quotientHessian_diagonal_eq_zero_of_inactive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦direction⟧ ⟦direction⟧ = 0 :=
  quotientHessian_eq_zero_of_inactive_first period hPeriod matterData kPlus kMinus robinMeasure
    frame llMeasure fields direction direction hInactive

theorem enrichedD9ActiveHessian_diagonal_eq_zero_of_inactive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point) = 0 :=
  enrichedD9ActiveHessian_eq_zero_of_inactive_first period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields sector column point direction direction hInactive

theorem fullMatterRobinTrueLLCurve_second_iteratedDeriv_eq_zero_of_inactive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    iteratedDeriv 2 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 := by
  rw [show (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) =
      fun _ : Real => fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction by
    funext t
    exact fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
      hInactive t]
  simp (discharger := fun_prop) [iteratedDeriv_const]

end
end P0EFTJanusFullMatterRobinTrueLLInactiveDiagonalOrderTwo4D
end JanusFormal
