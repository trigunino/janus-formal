import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

namespace JanusFormal
namespace P0EFTJanusThroatLinearOperationsZero4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod

@[simp] theorem throatPTPullback_zero
    (Fiber : Type) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] :
    throatPTPullback period hPeriod Fiber (0 : SmoothThroatField period hPeriod Fiber) = 0 := by
  exact (throatPTPullbackLinearMap period hPeriod Fiber).map_zero

@[simp] theorem ptAverage_zero (point : EffectiveThroat period hPeriod) :
    ptAverage period hPeriod (0 : EffectiveThroat period hPeriod → Real) point = 0 := by
  unfold ptAverage
  change (1 / 2 : Real) * (0 + 0) = 0
  ring

@[simp] theorem throatFrameDerivative_zero
    (Fiber : Type) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) (index : Fin frame.count) :
    throatFrameDerivative period hPeriod Fiber frame
      (0 : SmoothThroatField period hPeriod Fiber) point index = 0 := by
  rw [throatFrameDerivative_eq_mvfderiv]
  have hz : SmoothThroatField.toFun (0 : SmoothThroatField period hPeriod Fiber) =
      (0 : EffectiveThroat period hPeriod → Fiber) := by
    funext x
    rfl
  rw [hz]
  rw [mvfderiv_zero]
  simp

end
end P0EFTJanusThroatLinearOperationsZero4D
end JanusFormal
