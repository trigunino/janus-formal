import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGhostD9Variation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonAuxiliaryD9Kernel4D

namespace JanusFormal
namespace P0EFTJanusGhostAuxiliaryInactiveSectorNoether4D
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
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
open P0EFTJanusCommonGhostD9Variation4D
open P0EFTJanusCommonAuxiliaryD9Kernel4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def ghostFullDirection
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber) :
    FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric := (ghostOnlyIndependentVariation period hPeriod ghost).metrics
      matter := 0
      gauge := 0
      ghost := ghost
      auxiliary := 0
      ll := 0 }
  robin := 0
  llAuxMetric := 0
  llMeasure := 0

def auxiliaryFullDirection
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) : FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric := (auxiliaryOnlyIndependentVariation period hPeriod auxiliary).metrics
      matter := 0
      gauge := 0
      ghost := 0
      auxiliary := auxiliary
      ll := 0 }
  robin := 0
  llAuxMetric := 0
  llMeasure := 0

@[simp] theorem fullVariation_ghostFullDirection
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber) :
    (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1 =
      ghostOnlyIndependentVariation period hPeriod ghost := by
  rfl

@[simp] theorem fullVariation_auxiliaryFullDirection
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    (fullMatterRobinLLVariation period hPeriod (auxiliaryFullDirection period hPeriod auxiliary)).1 =
      auxiliaryOnlyIndependentVariation period hPeriod auxiliary := by
  rfl

@[simp] theorem activeProjection_ghostFullDirection
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber) :
    activeProjection period hPeriod (ghostFullDirection period hPeriod ghost) =
      zeroActiveDirection period hPeriod := by rfl

@[simp] theorem activeProjection_auxiliaryFullDirection
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    activeProjection period hPeriod (auxiliaryFullDirection period hPeriod auxiliary) =
      zeroActiveDirection period hPeriod := by rfl

theorem ghost_sector_curve_constant
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (t : Real) :
    P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D.fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      (ghostFullDirection period hPeriod ghost) t =
    P0EFTJanusFullMatterRobinTrueLLActionVariation4D.fullMatterRobinTrueLLAction period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction :=
  fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction _ rfl t

theorem auxiliary_sector_curve_constant
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber)
    (t : Real) :
    P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D.fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      (auxiliaryFullDirection period hPeriod auxiliary) t =
    P0EFTJanusFullMatterRobinTrueLLActionVariation4D.fullMatterRobinTrueLLAction period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction :=
  fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction _ rfl t

theorem ghost_sector_euler_zero
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber) :
    P0EFTJanusFullMatterRobinTrueLLActionVariation4D.fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction (ghostFullDirection period hPeriod ghost) = 0 :=
  fullMatterRobinTrueLLEuler_eq_zero_of_activeProjection_zero period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction _ rfl

theorem auxiliary_sector_euler_zero
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    P0EFTJanusFullMatterRobinTrueLLActionVariation4D.fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction (auxiliaryFullDirection period hPeriod auxiliary) = 0 :=
  fullMatterRobinTrueLLEuler_eq_zero_of_activeProjection_zero period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction _ rfl

theorem ghost_sector_hessian_zero
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (other : FullMatterRobinLLDirections period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber) :
    P0EFTJanusMatterRobinFullLLActualHessian4D.globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields (ghostFullDirection period hPeriod ghost) other = 0 :=
  globalMatterRobinFullLLHessian_inactive_left period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields _ other rfl

theorem auxiliary_sector_hessian_zero
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (other : FullMatterRobinLLDirections period hPeriod)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    P0EFTJanusMatterRobinFullLLActualHessian4D.globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields (auxiliaryFullDirection period hPeriod auxiliary) other = 0 :=
  globalMatterRobinFullLLHessian_inactive_left period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields _ other rfl

end
end P0EFTJanusGhostAuxiliaryInactiveSectorNoether4D
end JanusFormal
