import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLVariationalAPI4D

/-! Left and right kernels of the genuine symmetric full LL Hessian coincide. -/

namespace JanusFormal
namespace P0EFTJanusFullLLHessianKernelSymmetry4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullLLVariationalAPI4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def InLeftKernel
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (direction : FullMatterRobinLLDirections period hPeriod) : Prop :=
  ∀ test, fullLLHessian period hPeriod frame fields direction test mu = 0

def InRightKernel
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (direction : FullMatterRobinLLDirections period hPeriod) : Prop :=
  ∀ test, fullLLHessian period hPeriod frame fields test direction mu = 0

theorem inLeftKernel_iff_inRightKernel
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (direction : FullMatterRobinLLDirections period hPeriod) :
    InLeftKernel period hPeriod frame fields mu direction ↔
      InRightKernel period hPeriod frame fields mu direction := by
  constructor
  · intro h test
    rw [fullLLHessian_symmetric period hPeriod frame fields test direction mu]
    exact h test
  · intro h test
    rw [fullLLHessian_symmetric period hPeriod frame fields direction test mu]
    exact h test

end
end P0EFTJanusFullLLHessianKernelSymmetry4D
end JanusFormal
