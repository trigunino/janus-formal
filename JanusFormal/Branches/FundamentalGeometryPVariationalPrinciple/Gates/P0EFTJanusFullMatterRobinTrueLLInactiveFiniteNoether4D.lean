import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D

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
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- The zero reading in precisely the five slots seen by the true assembled
action. This is not asserted to be a global gauge direction. -/
def zeroActiveDirection : ActiveDirection period hPeriod where
  matter := 0
  robin := 0
  llField := 0
  llAuxMetric := 0
  llMeasure := 0

/-- Finite inactive Noether statement: if the active projection vanishes,
the true assembled action is constant along the entire affine translation. -/
theorem fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction =
      zeroActiveDirection period hPeriod) (t : Real) :
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction t =
      fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction := by
  have hMatter := congrArg ActiveDirection.matter hInactive
  have hRobin := congrArg ActiveDirection.robin hInactive
  have hField := congrArg ActiveDirection.llField hInactive
  have hAux := congrArg ActiveDirection.llAuxMetric hInactive
  have hMeasure := congrArg ActiveDirection.llMeasure hInactive
  change direction.common.matter = 0 at hMatter
  change direction.robin = 0 at hRobin
  change direction.common.ll = 0 at hField
  change direction.llAuxMetric = 0 at hAux
  change direction.llMeasure = 0 at hMeasure
  have hMatterComponents :
      matterVariationComponentFamily period hPeriod
        (0 : SmoothQuotientField period hPeriod MatterFiber ×
          SmoothQuotientField period hPeriod MatterFiber) = 0 := by
    funext index
    ext point
    unfold matterVariationComponentFamily
    by_cases hSector : index.1 = 0
    · simp only [hSector, if_true]
      exact map_zero (EuclideanSpace.proj index.2)
    · simp only [hSector, if_false]
      exact map_zero (EuclideanSpace.proj index.2)
  have hMatterCurve : matterMultipletAffineCurve period hPeriod
      (independentMatterComponentFamily period hPeriod fields) 0 t =
      independentMatterComponentFamily period hPeriod fields := by
    funext index
    ext point
    simp [matterMultipletAffineCurve, scalarAffineCurve]
  unfold fullMatterRobinTrueLLCurve fullMatterRobinTrueLLAction
  rw [hMatter, hRobin, hField, hAux, hMeasure]
  rw [hMatterComponents]
  rw [hMatterCurve]
  simp [junctionAffineCurve, differentialLLFullCurve]

/-- The same finite inactive curve has derivative zero at the base point. -/
theorem fullMatterRobinTrueLLCurve_inactive_hasDerivAt_zero
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction =
      zeroActiveDirection period hPeriod) :
    HasDerivAt (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod
      matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
      fields junction direction t) 0 0 := by
  rw [show (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      direction t) = fun _ : Real => fullMatterRobinTrueLLAction period hPeriod
        matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        fields junction by
    funext t
    exact fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero period
      hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
      llMeasure fields junction direction hInactive t]
  exact hasDerivAt_const 0 _

/-- Consequently the genuine Euler functional of the same action vanishes on
every direction with zero active projection. -/
theorem fullMatterRobinTrueLLEuler_eq_zero_of_activeProjection_zero
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
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction =
      zeroActiveDirection period hPeriod) :
    fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure fields junction direction = 0 := by
  have hZero := fullMatterRobinTrueLLCurve_inactive_hasDerivAt_zero period hPeriod
    matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields
    junction direction hInactive
  have hActual := fullMatterRobinTrueLLAction_hasDerivAt period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    direction
  exact hActual.unique hZero

end
end P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
end JanusFormal
